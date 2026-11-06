import Mathlib

open Real Set


/-
Define $\min\{f(x), g(x)\}$ as the smaller value between $f(x)$ and $g(x)$. Then, the range of the function $f(x) = \min\{2-x^2, x\}$ is \_\_\_\_\_.
-/

theorem algebra_9275
    (f : ℝ → ℝ)
    (hf : f = λ x => min (2 - x ^ 2) x) :
    range f = {y | y ≤ 1} := by

  unfold range
  apply Subset.antisymm

  -- {x | ∃ y, f y = x} ⊆ {y | y ≤ 1}
  -- f x ≤ 1
  . simp
    intro x
    by_cases h : -2 ≤ x ∧ x ≤ 1

    -- -2 ≤ x ∧ x ≤ 1
    . simp [hf]
      right
      linarith

    -- x < -2 ∨ 1 < x
    . rw [not_and] at h
      apply not_or_of_imp at h
      rw [not_le] at h
      simp [hf]
      rcases h with h | h
      . right
        linarith
      . left
        simp at h
        rw [pow_two]
        have : 1 * 1 < x * x := by
          refine mul_lt_mul_of_pos' h h Real.zero_lt_one ?_
          linarith
        linarith

  -- {y | y ≤ 1} ⊆ {x | ∃ y, f y = x}
  -- ∀ y ≤ 1, ∃ x, f x = y
  . simp
    intro y hy
    by_cases h : -2 ≤ y ∧ y ≤ 1
    . use y
      simp [hf]
      have : (y + 2) * (y - 1) ≤ 0 := by
        have r1 : 0 ≤ y + 2 := by linarith
        have r2 : y - 1 ≤ 0 := by linarith
        exact mul_nonpos_of_nonneg_of_nonpos r1 r2
      linarith
    . rw [not_and] at h
      apply not_or_of_imp at h
      rw [not_le] at h
      simp [hf]
      rcases h with h | h
      . use √ (2 - y)
        have r1 : 4 < 2 - y := by linarith
        have r2 : 2 < √ (2 - y) := by
          conv => lhs; rw [show 2 = √ 4 by simp [show (4 : ℝ) = 2 * 2 by norm_num]]
          refine (sqrt_lt_sqrt_iff_of_pos ?_).mpr ?_
          <;> linarith
        rw [min_eq_left_of_lt (by linarith [sq_nonneg (√ (2 - y))])]
        field_simp
      . contradiction
