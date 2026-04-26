/-
Query model: programs as free-monad trees over a parametric query type.
Vendored and simplified from Algolean.

Original authors: Tanner Duve, Shreyas Srinivas, Eric Wieser (Apache 2.0).
-/

import Algolean.FreeM
import Algolean.AddWriter
import Mathlib.Algebra.Group.Defs

namespace Algolean

/--
A model assigns to each query both an evaluation and a numeric cost.
-/
structure Model (QType : Type u → Type v) (Cost : Type w) where
  evalQuery : {ι : Type u} → QType ι → ι
  cost : {ι : Type u} → QType ι → Cost

abbrev Model.timeQuery
    {Q : Type u → Type v} {Cost : Type u} {ι : Type u}
    (M : Model Q Cost) (x : Q ι) : AddWriter Cost ι :=
  AddWriter.mk (M.evalQuery x) (M.cost x)

/-- A program is a free-monad tree of queries returning a value. -/
abbrev Prog (Q : Type u → Type v) (α : Type w) := FreeM Q α

namespace Prog

/-- The result of evaluating a program under a model. -/
def eval {Q : Type u → Type v} {α : Type u} {Cost : Type w}
    (P : Prog Q α) (M : Model Q Cost) : α :=
  Id.run <| P.liftM fun x => pure (M.evalQuery x)

@[simp]
theorem eval_pure {Q : Type u → Type v} {α : Type u} {Cost : Type w}
    (a : α) (M : Model Q Cost) :
    Prog.eval (FreeM.pure a) M = a :=
  rfl

@[simp]
theorem eval_liftBind {Q : Type u → Type v} {ι α : Type u} {Cost : Type w}
    (x : Q ι) (f : ι → Prog Q α) (M : Model Q Cost) :
    Prog.eval (FreeM.liftBind x f) M = Prog.eval (f (M.evalQuery x)) M :=
  rfl

@[simp]
theorem eval_bind {Q : Type u → Type v} {α β : Type u} {Cost : Type w}
    (x : Prog Q α) (f : α → Prog Q β) (M : Model Q Cost) :
    Prog.eval (FreeM.bind x f) M = Prog.eval (f (x.eval M)) M := by
  induction x with
  | pure a => rfl
  | liftBind op cont ih => exact ih (M.evalQuery op)

/-- The accumulated cost of running a program under a model. -/
def time {Q : Type u → Type v} {α Cost : Type u} [AddZero Cost]
    (P : Prog Q α) (M : Model Q Cost) : Cost :=
  (FreeM.liftM (m := AddWriter Cost) M.timeQuery P).tell

@[simp]
lemma time_pure {Q : Type u → Type v} {α Cost : Type u} [AddZero Cost]
    (a : α) (M : Model Q Cost) :
    Prog.time (FreeM.pure a) M = (0 : Cost) := by
  show (FreeM.liftM (m := AddWriter Cost) M.timeQuery (FreeM.pure a)).tell = (0 : Cost)
  rw [FreeM.liftM_pure]
  exact AddWriter.tell_pure a

@[simp]
theorem time_liftBind {Q : Type u → Type v} {ι α Cost : Type u}
    [AddZero Cost]
    (x : Q ι) (f : ι → Prog Q α) (M : Model Q Cost) :
    Prog.time (FreeM.liftBind x f) M = M.cost x + Prog.time (f (M.evalQuery x)) M := by
  show (FreeM.liftM (m := AddWriter Cost) M.timeQuery (FreeM.liftBind x f)).tell = _
  rw [FreeM.liftM_liftBind]
  show (M.timeQuery x >>= fun b =>
    FreeM.liftM (m := AddWriter Cost) M.timeQuery (f b)).tell = _
  rw [AddWriter.tell_bind]
  rfl

@[simp]
lemma time_bind {Q : Type u → Type v} {α β Cost : Type u}
    [AddCommMonoid Cost] (M : Model Q Cost)
    (op : Prog Q α) (cont : α → Prog Q β) :
    Prog.time (op.bind cont) M =
      Prog.time op M + Prog.time (cont (Prog.eval op M)) M := by
  induction op with
  | pure a => simp
  | liftBind op cont' ih =>
    show Prog.time (FreeM.liftBind op (fun z => (cont' z).bind cont)) M = _
    rw [time_liftBind, ih (M.evalQuery op)]
    show M.cost op + (Prog.time (cont' (M.evalQuery op)) M
      + Prog.time (cont (Prog.eval (cont' (M.evalQuery op)) M)) M) =
      Prog.time (FreeM.liftBind op cont') M + _
    rw [time_liftBind, add_assoc, eval_liftBind]

end Prog

end Algolean
