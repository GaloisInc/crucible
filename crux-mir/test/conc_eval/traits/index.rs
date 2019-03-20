// FAIL: not sure why
pub trait Ind<Idx> 
where
    Idx: ?Sized, 
{
    type Output: ?Sized;
    fn index(&self, index: Idx) -> &Self::Output;
}

pub trait IndMut<Idx>: Ind<Idx> 
where
    Idx: ?Sized, 
{
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
}
