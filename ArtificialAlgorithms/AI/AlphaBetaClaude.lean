/-
Alpha-Beta Pruning Algorithm for perfect-information zero-sum games
Done by Claude Sonnet 4 and Opus 4
See blog post https://gasstationmanager.github.io/ai/2025/07/06/leantool-updates.html for more details
Note that this was done with a slightly different signature for GameTree than AlphaBeta.lean
-/

import Plausible
import Std
import Mathlib.Tactic.Linarith

namespace AlphaBetaClaude

open Plausible

-- Fixed maxV value
def maxVal : Int := 100
theorem maxVal_pos : maxVal > 0 := by decide

inductive GameTree where
| terminal (value: Int) -- Simplified
| node (children: List GameTree)
deriving Repr -- Restored

def minimax: (game: GameTree) -> Int
| GameTree.terminal v => v -- Simplified
| GameTree.node [] => -maxVal
| GameTree.node (child::tail) =>
    let r:= - minimax child
    max r (minimax (GameTree.node tail))
termination_by game => game

inductive ABResult(g: GameTree) (alpha beta: Int) where
|lb (p: beta <= minimax g)
|ub (p: alpha >= minimax g)
|value (x:Int) (p: x=minimax g)

instance: Shrinkable GameTree where
  shrink t := match t with
  | GameTree.terminal _ => [] -- Simplified
  | GameTree.node [] => []
  | GameTree.node (_::tail) => [GameTree.node tail]

instance: SampleableExt GameTree :=
SampleableExt.mkSelfContained do
let rec helper (level:Nat) : Gen GameTree := do
  let isTerm← SampleableExt.interpSample Bool
  if level=0 ∨  isTerm then
    let x ← SampleableExt.interpSample Int
    let x' := min (max x (-maxVal + 1)) (maxVal - 1) -- Ensure value is in a range, though not formally proven here
    return GameTree.terminal x' -- Simplified, proofs removed
  else
    let isNil ← SampleableExt.interpSample Bool
    if isNil then
      return GameTree.node []
    else
      let ch ← Gen.listOf (Gen.resize (fun x => min 8 x) do helper (level-1))
      return GameTree.node ch
let maxDepth := 5
let nl ← Gen.choose Nat 0 maxDepth (by omega)
helper nl

def alphabeta (g: GameTree) (alpha beta: Int)
(pa: alpha >= -maxVal) (pb: beta <= maxVal) (pab : alpha < beta)
: IO (ABResult g alpha beta) := do
match g with
| GameTree.terminal x => return ABResult.value x (by simp[minimax]) 
| GameTree.node [] => return ABResult.value (-maxVal) (by simp[minimax])
| GameTree.node (child::tail) =>
    let r ← alphabeta child (-beta) (-alpha) (by linarith) (by linarith) (by linarith)
    match r with
    | ABResult.value x prf =>
      let candidate := -x
      if h_cand_beta: candidate >= beta then
        return ABResult.lb (by simp [minimax, candidate, prf] at *; omega)
      else
        let newAlpha := max alpha candidate
        let tailResult ← alphabeta (GameTree.node tail) newAlpha beta (by omega) (by assumption) (by omega)
        match h_tail: tailResult with
        | ABResult.value y _ =>
          let finalCandidate := max candidate y
          return ABResult.value finalCandidate (by simp [minimax]; omega)
        | ABResult.lb p_tail =>
          -- Tail value >= beta, so overall value >= beta
          return ABResult.lb (by simp [minimax]; right; exact p_tail)
        | ABResult.ub p_tail =>
          -- p_tail: newAlpha >= minimax (GameTree.node tail)
          -- Case analysis on whether alpha >= candidate
          if h_alpha_cand: alpha >= candidate then
            -- If alpha >= candidate, then newAlpha = alpha
            -- We can prove alpha >= minimax (GameTree.node (child :: tail))
            return ABResult.ub (by 
              simp [minimax] at *
              -- newAlpha = alpha since alpha >= candidate
              have h_newAlpha : newAlpha = alpha := by simp [newAlpha, max_eq_left h_alpha_cand]
              rw [h_newAlpha] at p_tail
              constructor
              · -- alpha >= -minimax child since alpha >= candidate = -minimax child
                rw [← prf]; exact h_alpha_cand
              · exact p_tail  -- alpha >= minimax (GameTree.node tail)
            )
          else
            -- If alpha < candidate, then newAlpha = candidate  
            -- Since candidate >= minimax tail, the overall value is candidate
            -- Since alpha < candidate, we should return the exact value candidate
            return ABResult.value candidate (by
              simp [minimax]
              -- Goal: candidate = max (-minimax child) (minimax (GameTree.node tail))
              -- We have: candidate = -x and x = minimax child and candidate >= minimax (GameTree.node tail)
              have h_newAlpha : newAlpha = candidate := by simp [newAlpha, max_eq_right (le_of_not_ge h_alpha_cand)]
              rw [h_newAlpha] at p_tail
              -- candidate = -x = -minimax child, so candidate >= minimax tail means -minimax child >= minimax tail
              have h_equiv : candidate = -minimax child := by simp [candidate]; rw [← prf]
              rw [h_equiv] at p_tail
              rw [h_equiv]
              exact (max_eq_left p_tail).symm
            )
    | ABResult.lb prf =>
      -- prf: -alpha <= minimax child (the second argument to the recursive call)
      -- This doesn't give us enough info about the parent, so continue with tail
      let tailResult ← alphabeta (GameTree.node tail) alpha beta (by assumption) (by assumption) (by assumption)
      match tailResult with
      | ABResult.value y p_tail_val =>
        -- We know -minimax child <= alpha (from prf)
        -- The overall value is max(-minimax child, y)
        -- But we don't know -minimax child exactly, just that it's <= alpha
        -- If y >= alpha, then max(-minimax child, y) = y
        -- If y < alpha, then we can't determine the exact value
        if h_y_alpha: y >= alpha then
          return ABResult.value y (by 
            simp [minimax, p_tail_val]
            -- Need to show: y = max (-minimax child) y
            -- Since -minimax child <= alpha <= y, we have max(-minimax child, y) = y
            have h1: -minimax child <= alpha := by linarith [prf]
            have h2: -minimax child <= y := by linarith [h1, h_y_alpha]
            omega
          )
        else
          -- y < alpha, and -minimax child <= alpha
          -- The max could be anywhere from y to alpha
          return ABResult.ub (by
            simp [minimax]
            -- Goal: alpha >= max (-minimax child) (minimax (GameTree.node tail))
            -- We have: -alpha <= minimax child, so -minimax child <= alpha
            -- We have: y = minimax (GameTree.node tail) and y < alpha from h_y_alpha
            have h1: -minimax child ≤ alpha := by linarith [prf]
            have h2: minimax (GameTree.node tail) < alpha := by rw [← p_tail_val]; linarith [h_y_alpha]
            constructor
            · exact h1  -- alpha >= -minimax child  
            · linarith [h2]  -- alpha >= minimax (GameTree.node tail)
          )
      | ABResult.lb p_tail2 =>
        return ABResult.lb (by simp [minimax]; right; exact p_tail2)
      | ABResult.ub p_tail3 =>
        return ABResult.ub (by
          simp [minimax]
          -- Goal: alpha >= max (-minimax child) (minimax (GameTree.node tail))
          -- We have: -alpha <= minimax child, so -minimax child <= alpha
          -- We have: alpha >= minimax (GameTree.node tail) from p_tail3
          have h1: -minimax child ≤ alpha := by linarith [prf]
          constructor
          · exact h1  -- alpha >= -minimax child
          · exact p_tail3  -- alpha >= minimax (GameTree.node tail)
        )
    | ABResult.ub prf =>
      -- prf: -beta >= minimax child
      -- This means -minimax child >= beta, so we should prune (beta cutoff)
      return ABResult.lb (by simp [minimax]; left; linarith)

def search (g: GameTree) : IO Int := do
  let result ← alphabeta g (-maxVal) maxVal (by decide) (by decide) (by decide)
  match result with
  | ABResult.value x _ => return x
  | ABResult.lb _ => return maxVal
  | ABResult.ub _ => return (-maxVal)

end AlphaBetaClaude
