/-
AddWriter monad (vendored from Algolean/Cslib).

Original author: Sorrachai Yingchareonthawornchai (Apache 2.0).
-/

import Mathlib.Algebra.Group.Defs

namespace Algolean

/-- A writer monad over an additive cost. -/
@[ext]
structure AddWriter (w : Type*) (α : Type*) where
  ret : α
  tell : w

namespace AddWriter

protected def pure [Zero T] {α} (a : α) : AddWriter T α :=
  ⟨a, 0⟩

instance [Zero T] : Pure (AddWriter T) where
  pure := AddWriter.pure

protected def bind {α β} [Add T] (m : AddWriter T α) (f : α → AddWriter T β) : AddWriter T β :=
  let r := f m.ret
  ⟨r.ret, m.tell + r.tell⟩

instance [Add T] : Bind (AddWriter T) where
  bind := AddWriter.bind

instance : Functor (AddWriter T) where
  map f x := ⟨f x.ret, x.tell⟩

instance [Add T] : Seq (AddWriter T) where
  seq f x := ⟨f.ret (x ()).ret, f.tell + (x ()).tell⟩

instance [Add T] : SeqLeft (AddWriter T) where
  seqLeft x y := ⟨x.ret, x.tell + (y ()).tell⟩

instance [Add T] : SeqRight (AddWriter T) where
  seqRight x y := ⟨(y ()).ret, x.tell + (y ()).tell⟩

instance [AddZero T] : Monad (AddWriter T) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map
  seq := Seq.seq
  seqLeft := SeqLeft.seqLeft
  seqRight := SeqRight.seqRight

@[simp] theorem ret_pure {α} [Zero T] (a : α) : (pure a : AddWriter T α).ret = a := rfl

@[simp] theorem ret_bind {α β} [Add T] (m : AddWriter T α) (f : α → AddWriter T β) :
    (m >>= f).ret = (f m.ret).ret := rfl

@[simp] theorem tell_bind {α β} [Add T] (m : AddWriter T α) (f : α → AddWriter T β) :
    (m >>= f).tell = m.tell + (f m.ret).tell := rfl

@[simp] theorem tell_pure {α} [Zero T] (a : α) : (pure a : AddWriter T α).tell = 0 := rfl

end AddWriter
end Algolean
