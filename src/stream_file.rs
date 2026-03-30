use core::cmp::min;

use crate::{Bpb, NextClusterError, ReadClusterInfo, StateMachine};

enum StreamFileState<'a> {
    Streaming {
        bpb: &'a Bpb,
        file_size: u32,
        cluster_number: u32,
        position: u32,
        end_of_cluster: bool,
    },
    Done(Result<(), StreamError>),
}

pub struct StreamFile<'a> {
    state: StreamFileState<'a>,
}

impl<'a> StreamFile<'a> {
    pub fn new(bpb: &'a Bpb, file_size: u32, start_cluster_number: u32) -> Self {
        Self {
            state: StreamFileState::Streaming {
                bpb,
                file_size,
                cluster_number: start_cluster_number,
                position: 0,
                end_of_cluster: false,
            },
        }
    }
}

#[derive(Debug)]
pub enum StreamInput<'a> {
    Next,
    ClusterInfo(&'a [u8]),
}

#[derive(Debug)]
pub struct Cluster {
    pub address: u64,
    pub len: u32,
}

#[derive(Debug, Clone, Copy)]
pub enum StreamError {
    NoNextCluster,
    NextCluster(NextClusterError),
}

#[derive(Debug)]
pub enum StreamOutput {
    Done,
    Cluster(Cluster),
    ReadClusterInfo(ReadClusterInfo),
}

impl StateMachine for StreamFile<'_> {
    type Output = Result<StreamOutput, StreamError>;
    type Input<'a> = StreamInput<'a>;

    fn output(&self) -> Self::Output {
        match &self.state {
            StreamFileState::Streaming {
                bpb,
                file_size,
                cluster_number,
                position,
                end_of_cluster,
            } => {
                if *end_of_cluster {
                    Ok(StreamOutput::ReadClusterInfo(ReadClusterInfo {
                        address_in_partition: bpb.cluster_info_start(*cluster_number),
                        len: bpb.cluster_info_size(),
                    }))
                } else {
                    Ok(StreamOutput::Cluster(Cluster {
                        address: bpb.cluster_position(*cluster_number),
                        len: min(bpb.bytes_per_cluster(), *file_size - *position),
                    }))
                }
            }
            StreamFileState::Done(Ok(())) => Ok(StreamOutput::Done),
            StreamFileState::Done(Err(e)) => Err(*e),
        }
    }

    fn input(&mut self, input: Self::Input<'_>) {
        match &mut self.state {
            StreamFileState::Streaming {
                bpb,
                file_size,
                cluster_number,
                position,
                end_of_cluster,
            } => {
                if !*end_of_cluster {
                    assert!(matches!(input, StreamInput::Next));
                    *position += min(bpb.bytes_per_cluster(), *file_size - *position);
                    if *position < *file_size {
                        *end_of_cluster = true;
                    } else {
                        self.state = StreamFileState::Done(Ok(()))
                    }
                } else {
                    let cluster_info = match input {
                        StreamInput::ClusterInfo(cluster_info) => cluster_info,
                        _ => unreachable!(),
                    };
                    match bpb.next_cluster_number(cluster_info) {
                        Ok(Some(next_cluster_number)) => {
                            *cluster_number = next_cluster_number;
                            *end_of_cluster = false;
                        }
                        Ok(None) => {
                            self.state = StreamFileState::Done(Err(StreamError::NoNextCluster));
                        }
                        Err(e) => {
                            self.state = StreamFileState::Done(Err(StreamError::NextCluster(e)));
                        }
                    }
                }
            }
            _ => unreachable!(),
        }
    }
}
