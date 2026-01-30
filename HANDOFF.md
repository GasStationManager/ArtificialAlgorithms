# Handoff: Completing Sliding Window Proofs

## File Location
`ArtificialAlgorithms/SlidingWindow/MaxLengthSumAtMostK.lean`

## Context
This file implements a verified O(n) sliding window algorithm for finding the maximum length subarray with sum at most K. The algorithm is fully functional and all test cases pass.

## Current Status: 4 Remaining Sorries

### 1. Core Lemma: `shrinkUntilValid_minimal` (line ~196)

```lean
theorem shrinkUntilValid_minimal (s : WindowState a k) (l : Nat)
    (hlLower : s.left ≤ l) (hlUpper : l < s.shrinkUntilValid.val.left) :
    subarraySum a l s.shrinkUntilValid.val.right > k
```

**What it says:** For any `l` in `[initial.left, result.left)`, the sum of window `[l, right)` is > k.

**Proof strategy:**
1. Unfold `shrinkUntilValid` and split on the three cases:
   - `s.sum ≤ k`: Returns immediately, so `result.left = s.left`. No `l` satisfies `s.left ≤ l < s.left`.
   - `s.sum > k` and `s.left = s.right`: Empty window, same as above.
   - `s.sum > k` and `s.left < s.right`: Recursive case.
     - For `l = s.left`: sum = `s.sum > k` ✓
     - For `l > s.left`: Use induction on the recursive call

**Technical challenge:** The `split_ifs` tactic doesn't properly simplify the goal after unfolding because of how the Subtype is constructed. You may need to:
- Use `conv` tactics to rewrite inside the goal
- Or restructure using `generalize` to name the result
- Or prove a helper that avoids the Subtype pattern

### 2-4. Applications in `step` (lines ~444, ~460, ~500)

These three sorries all need `shrinkUntilValid_minimal` but face a type barrier:
- `shrunk` comes from pattern matching: `let ⟨shrunk, hShrunk, hShrunkRight⟩ := extended.shrinkUntilValid`
- This creates `shrunk : WindowState a k` but Lean doesn't unify it with `extended.shrinkUntilValid.val`

**Options to fix:**
1. Avoid pattern matching - use `extended.shrinkUntilValid.val` directly throughout `step`
2. Add a lemma that connects pattern-matched variables to `.val`
3. Use `show` or `change` tactics with explicit type conversions

## What's Already Proven

- `subarraySum_extend_right`: O(1) window extension
- `subarraySum_shrink_left`: O(1) window shrinking
- `subarraySum_mono_left`: Smaller left index → larger sum (for non-negative arrays)
- `valid_window_mono_left`: Monotonicity of valid windows
- `step_right_eq`: Each step advances right by 1
- `mainLoop_right_eq_size`: Loop processes entire array
- `hLeftMinimal` invariant: Added to `LoopState` to track that current left is minimal

## Key Structures

```lean
structure WindowState (a : Array Nat) (k : Nat) where
  left : Nat
  right : Nat
  sum : Nat
  hLeftBound : left ≤ right
  hRightBound : right ≤ a.size
  hSum : sum = subarraySum a left right

structure LoopState (a : Array Nat) (k : Nat) extends WindowState a k where
  bestLen : Nat
  hBestAchievable : ∃ l r, ... -- achievability proof
  hBestOptimal : ∀ l r, ... -- optimality proof
  hLeftMinimal : ∀ l, l < left → subarraySum a l right > k  -- NEW
```

## Build & Test

```bash
cd ~/src/ArtificialAlgorithms
lake build                    # Should complete with sorry warnings
lake env lean ArtificialAlgorithms/SlidingWindow/MaxLengthSumAtMostK.lean
```

Test outputs should be: 3, 3, 0, 5, 3

## Suggested Approach

1. First solve `shrinkUntilValid_minimal` using strong induction:
   ```lean
   induction s.right - s.left using Nat.strongRecOn generalizing s l
   ```

2. Handle the Subtype carefully - consider defining:
   ```lean
   def shrinkUntilValid' (s : WindowState a k) : WindowState a k × Prop × Prop :=
     let result := s.shrinkUntilValid
     (result.val, result.property.1, result.property.2)
   ```
   Then prove properties about this simpler form.

3. Once the lemma works, the three applications in `step` should follow by connecting `shrunk` to `extended.shrinkUntilValid.val`.

## Files Modified

- `ArtificialAlgorithms/SlidingWindow/MaxLengthSumAtMostK.lean` - main file
- `ArtificialAlgorithms.lean` - added import for the new module
