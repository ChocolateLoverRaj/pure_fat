pub trait StateMachine {
    type Input<'a>;
    type Output;

    fn output(&self) -> Self::Output;
    fn input(&mut self, input: Self::Input<'_>);
}
