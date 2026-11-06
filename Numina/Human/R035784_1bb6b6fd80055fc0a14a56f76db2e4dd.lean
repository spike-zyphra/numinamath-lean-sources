import Mathlib

/-
What is $( - 1)^1 + ( - 1)^2 + \cdots + ( - 1)^{2006}$?

(A) -2006 (B) -1 (C) 0 (D) 1 (E) 2006
-/

theorem algebra_97764
  : ∑ i ∈ Finset.range 2006, (-1)^(i + 1) = 0
:= by
  -- Note that the partial sums alternate between `0` and `-1`, so we prove this by induction, keeping track of the parity of the previous term
  have : ∀ (k : ℕ), ∑ i ∈ Finset.range k, (-1)^(i + 1) = if Even k then 0 else -1 := by
    intro k
    induction' k with k ih
    . simp
    . rw [Finset.sum_range_succ, ih]
      by_cases h : Even k
      . have : ¬Even (k + 1) := by simp [h]
        simp [h, this]
      . have : Even (k + 1) := by
          rw [← Nat.not_odd_iff_even]
          rw [Nat.not_even_iff_odd] at h
          simp [h]
        simp [h, this]
  -- Applying this to the `Even 2006` case, we're done
  rw [this 2006]
  norm_num
  decide