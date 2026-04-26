/-
Free monad (vendored, simplified from Cslib).

Original authors: Tanner Duve, Eric Wieser (Apache 2.0).
Adapted for Lean 4.26.0 without Cslib/module syntax.
-/

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Common

namespace Algolean

/-- Free monad over a type constructor `F`. -/
inductive FreeM.{u, v, w} (F : Type u → Type v) (α : Type w) where
  | protected pure (a : α) : FreeM F α
  | liftBind {ι : Type u} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

universe u v w w' w''

namespace FreeM
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''}

instance : Pure (FreeM F) where pure := .pure

@[simp]
theorem pure_eq_pure : (pure : α → FreeM F α) = FreeM.pure := rfl

protected def bind (x : FreeM F α) (f : α → FreeM F β) : FreeM F β :=
  match x with
  | .pure a => f a
  | .liftBind op cont => .liftBind op fun z => FreeM.bind (cont z) f

protected theorem bind_assoc (x : FreeM F α) (f : α → FreeM F β) (g : β → FreeM F γ) :
    (x.bind f).bind g = x.bind (fun x => (f x).bind g) := by
  induction x with
  | pure a => rfl
  | liftBind op cont ih =>
    simp [FreeM.bind] at *
    simp [ih]

instance : Bind (FreeM F) where bind := .bind

@[simp]
theorem bind_eq_bind {α β : Type w} :
    Bind.bind = (FreeM.bind : FreeM F α → _ → FreeM F β) := rfl

@[simp]
def map (f : α → β) : FreeM F α → FreeM F β
  | .pure a => .pure (f a)
  | .liftBind op cont => .liftBind op fun z => FreeM.map f (cont z)

@[simp]
theorem id_map : ∀ x : FreeM F α, map id x = x
  | .pure a => rfl
  | .liftBind op cont => by simp_all [map, id_map]

theorem comp_map (h : β → γ) (g : α → β) : ∀ x : FreeM F α, map (h ∘ g) x = map h (map g x)
  | .pure a => rfl
  | .liftBind op cont => by simp_all [map, comp_map]

instance : Functor (FreeM F) where
  map := .map

@[simp]
theorem map_eq_map {α β : Type w} :
    Functor.map = FreeM.map (F := F) (α := α) (β := β) := rfl

def lift (op : F ι) : FreeM F ι :=
  .liftBind op .pure

@[simp]
lemma lift_def (op : F ι) :
    (lift op : FreeM F ι) = liftBind op .pure := rfl

@[simp]
lemma pure_bind (a : α) (f : α → FreeM F β) : (.pure a : FreeM F α).bind f = f a := rfl

@[simp]
lemma bind_pure : ∀ x : FreeM F α, x.bind (.pure) = x
  | .pure a => rfl
  | liftBind op k => by simp [FreeM.bind, bind_pure]

@[simp]
lemma bind_pure_comp (f : α → β) : ∀ x : FreeM F α, x.bind (.pure ∘ f) = map f x
  | .pure a => rfl
  | liftBind op k => by simp only [FreeM.bind, map, bind_pure_comp]

@[simp]
lemma liftBind_bind (op : F ι) (cont : ι → FreeM F α) (f : α → FreeM F β) :
    (liftBind op cont).bind f = liftBind op fun x => (cont x).bind f := rfl

instance : LawfulFunctor (FreeM F) where
  map_const := rfl
  id_map := id_map
  comp_map _ _ := comp_map _ _

instance : Monad (FreeM F) where

instance : LawfulMonad (FreeM F) := LawfulMonad.mk'
  (bind_pure_comp := bind_pure_comp)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := FreeM.bind_assoc)

section liftM
variable {m : Type u → Type w} [Monad m] {α β : Type u}

protected def liftM (interp : {ι : Type u} → F ι → m ι) : FreeM F α → m α
  | .pure a => pure a
  | .liftBind op cont => interp op >>= fun result => (cont result).liftM interp

@[simp]
lemma liftM_pure (interp : {ι : Type u} → F ι → m ι) (a : α) :
    (.pure a : FreeM F α).liftM interp = pure a := rfl

@[simp]
lemma liftM_liftBind (interp : {ι : Type u} → F ι → m ι) (op : F β) (cont : β → FreeM F α) :
    (liftBind op cont).liftM interp = (do let b ← interp op; (cont b).liftM interp) := by
  rfl

@[simp]
lemma liftM_bind [LawfulMonad m]
    (interp : {ι : Type u} → F ι → m ι) (x : FreeM F α) (f : α → FreeM F β) :
    (x.bind f).liftM interp = (do let a ← x.liftM interp; (f a).liftM interp) := by
  induction x generalizing f with
  | pure a => simp only [pure_bind, liftM_pure, LawfulMonad.pure_bind]
  | liftBind op cont ih =>
    rw [FreeM.bind, liftM_liftBind, liftM_liftBind, bind_assoc]
    congr 1
    funext a
    exact ih a f

end liftM

end FreeM

end Algolean
