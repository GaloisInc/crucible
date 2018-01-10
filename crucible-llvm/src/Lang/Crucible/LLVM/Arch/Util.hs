module Lang.Crucible.LLVM.Arch.Util where



(|->) :: a -> b -> (a, b)
p |-> x = (p,x)
