/-
Alpha-Beta Pruning Algorithm for perfect-information zero-sum games
Done by o3 and GPT 4.1, with LeanTool on Cursor
See blog post https://gasstationmanager.github.io/ai/2025/06/08/proving-alphabeta.html for more details.
-/

import Plausible
import Std
open Plausible


-- Fixed maxV value
def maxVal : Int := 100
theorem maxVal_pos : maxVal > 0 := by decide

inductive GameTree where
|terminal  (value: Int) (pmin:value>= -maxVal)(pmax:value<=maxVal)
|node (children: List GameTree)
deriving Repr

def minimax: (game: GameTree) -> Int
|GameTree.terminal v _ _ => v
|GameTree.node [] => -maxVal
|GameTree.node (child::tail) =>
    let r:= - minimax child
    max r (minimax (GameTree.node tail))
termination_by game => game

inductive ABResult(g: GameTree) (alpha beta: Int) where
|lb (p: beta <= minimax g) --when beta is a lower bound of the real minimax value
|ub (p: alpha >= minimax g) --when alpha is an upper bound of the real minimax value
|value (x:Int) (p: x=minimax g)

instance: Shrinkable GameTree where
  shrink t := match t with
  |GameTree.terminal _ _ _ => []
  |GameTree.node [] => []
  |GameTree.node (_::tail) => [GameTree.node tail]

instance: SampleableExt GameTree :=
SampleableExt.mkSelfContained do
let rec helper (level:Nat) : Gen GameTree := do
  let isTerm← SampleableExt.interpSample Bool
  if level=0 ∨  isTerm then
    -- Generate a value between -maxVal and maxVal
    let x ← SampleableExt.interpSample Int
    let x' := min (max x (-maxVal + 1)) (maxVal - 1)
    return GameTree.terminal x' (by
      have h1 : maxVal = 100 := rfl
      have h2 : maxVal > 0 := maxVal_pos
      have h3 : -maxVal + 1 ≥ -maxVal := by omega
      have h4 : min (max x (-maxVal + 1)) (maxVal - 1) ≥ -maxVal + 1 := by omega
      omega
    ) (by
      have h1 : maxVal = 100 := rfl
      have h2 : maxVal > 0 := maxVal_pos
      have h3 : maxVal - 1 ≤ maxVal := by omega
      have h4 : min (max x (-maxVal + 1)) (maxVal - 1) ≤ maxVal - 1 := by omega
      omega
    )
  else
    let ch ← Gen.listOf (Gen.resize (fun x => min 4 x) do helper (level-1))
    return GameTree.node ch
-- Increase depth to 4
let maxDepth := 4
let nl ← Gen.choose Nat 0 maxDepth (by omega)
helper nl


def alphabeta (g: GameTree) (alpha beta: Int)
(pa: alpha >= -maxVal) (pb: beta <= maxVal)
(pab: alpha < beta)
: ABResult g alpha beta :=
match g with
|GameTree.terminal x _ _ => ABResult.value x (by simp[minimax])
|GameTree.node [] => ABResult.value (-maxVal) (by simp[minimax])
|GameTree.node (child::tail) =>
   let r := alphabeta child (-beta) (-alpha) (by omega) (by omega) (by omega)
   match r with
   | ABResult.value x prf =>
       let v := -x
       if hvb: v >= beta then
         ABResult.lb (by
           rw [minimax]; omega
         )
       else
         let newAlpha := max alpha v
         let rest := alphabeta (GameTree.node tail) newAlpha beta (by omega) (by omega) (by omega)
         -- For now, only handle ABResult.value for rest, stub for others
         match rest with
         | ABResult.lb prf => ABResult.lb (by simp [minimax]; omega)
         | ABResult.ub prf =>
             let candidate := max v newAlpha
             if hac: alpha >= candidate then
               ABResult.ub (by simp [minimax]; omega)
             else
               ABResult.value candidate (by simp [minimax, candidate]; omega)
         | ABResult.value y prf2 =>
             let candidate := max v y
             ABResult.value candidate (by
               simp [candidate, v, prf, prf2, minimax])
   | ABResult.lb prf =>
       let rtail := alphabeta (GameTree.node tail) alpha beta pa pb pab
       match rtail with
       | ABResult.lb prf2 =>
           ABResult.lb (by simp [minimax]; omega)
       | ABResult.ub prf2 =>
           ABResult.ub (by simp [minimax]; omega)
       | ABResult.value y prf2 =>
           if hya : y >= alpha then
             ABResult.value y (by
               simp[minimax] at *;
               omega)
           else
             ABResult.ub (by
               simp[minimax] at *;
               omega)
   | ABResult.ub prf =>
       ABResult.lb (by
         simp [minimax]; omega)

def alphabeta_main (g : GameTree) : ABResult g (-maxVal) maxVal :=
  alphabeta g (-maxVal) maxVal (by decide) (by decide) (by decide)




