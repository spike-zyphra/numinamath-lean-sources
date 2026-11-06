import Mathlib

/- Find the set consisting of all real values of $x$ such that the three numbers $2^{x}, 2^{x^{2}}, 2^{x^{3}}$ form a non-constant arithmetic progression (in that order).-/
theorem algebra_611044 :
    {x : ℝ | ∃ d : ℝ, d ≠ 0 ∧ 2 ^ x ^ 2 = 2 ^ x + d ∧ 2 ^ x ^ 3 = 2 ^ x ^ 2 + d} = ∅ := by
  -- Simplify the goal.
  ext x
  refine ⟨?_, by tauto⟩
  rintro ⟨d, h₀, h₁, h₂⟩
  -- Show first that x ≠ 0.
  have h₃ : x ≠ 0 := by
    -- Otherwise, d = 0.
    by_contra!
    simp_all
  -- Show also that x ≠ 1.
  have h₄ : x ≠ 1 := by
    -- Otherwise, d = 0 again.
    by_contra!
    simp_all
  -- Prove the AM-GM inequality of two variables.
  have AM_GM_ineq_2 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : x + y ≥ 2 * Real.sqrt (x * y) := by
    have := sq_nonneg (Real.sqrt x - Real.sqrt y)
    rw [sub_sq, mul_assoc, <-Real.sqrt_mul, Real.sq_sqrt, Real.sq_sqrt] at this
    linarith only [this]
    assumption'
  -- We have 2 * 2 ^ (x ^ 2) = 2 ^ x + 2 ^ (x ^ 3) ≥ 2√(2 ^ x * 2 ^ (x ^ 3)).
  have h₅ : (2 : ℝ) * 2 ^ x ^ 2 ≥ 2 * 2 ^ ((x + x ^ 3) / 2) := by
    calc
      _ = (2 : ℝ) ^ x + 2 ^ x ^ 3 := by
        rw [two_mul]
        nth_rw 1 [h₁, h₂]
        ring
      _ ≥ 2 * Real.sqrt (2 ^ x * 2 ^ x ^ 3) := by
        apply AM_GM_ineq_2
        <;> positivity
      _ = 2 * 2 ^ ((x + x ^ 3) / 2) := by
        rw [Real.sqrt_eq_rpow, <-Real.rpow_add, <-Real.rpow_mul, mul_one_div]
        <;> norm_num
  rw [ge_iff_le, mul_le_mul_left (by norm_num), Real.rpow_le_rpow_left_iff (by norm_num)] at h₅
  -- We get x (x - 1)² ≤ 0.
  replace h₅ : x * (x - 1) ^ 2 ≤ 0 := by
    linarith only [h₅]
  -- Since (x - 1)² > 0 and x ≠ 0, we get x < 0.
  have h₆ : 0 < (x - 1) ^ 2 := by
    by_contra!
    replace this : (x - 1) ^ 2 = 0 := by
      linarith only [sq_nonneg (x - 1), this]
    simp at this
    absurd h₄
    linarith only [h₄, this]
  replace h₅ : x < 0 := by
    apply lt_of_le_of_ne
    . nlinarith only [h₅, h₆]
    . exact h₃
  -- Now we get a contradiction.
  suffices (2 : ℝ) > 2 by
    simp at this
  calc
    _ = (2 : ℝ) ^ (0 : ℝ) + (2 : ℝ) ^ (0 : ℝ) := by norm_num
    _ > (2 : ℝ) ^ x + 2 ^ x ^ 3 := by
      -- We have 2 > 2 ^ x + 2 ^ x ^ 3 because x and x ^ 3 are negative.
      apply add_lt_add
      . rw [Real.rpow_lt_rpow_left_iff (by norm_num)]
        exact h₅
      . rw [Real.rpow_lt_rpow_left_iff (by norm_num)]
        nlinarith only [h₅, show 0 < x ^ 2 by positivity]
    _ = 2 * 2 ^ x ^ 2 := by
      -- We have 2 * 2 ^ x ^ 2 = 2 ^ x + 2 ^ x ^ 3.
      rw [two_mul]
      nth_rw 1 [h₁, h₂]
      ring
    _ > 2 * (2 ^ (0 : ℝ)) := by
      -- We have 2 ^ x > 1 because x < 0.
      rw [gt_iff_lt, mul_lt_mul_left (by norm_num), Real.rpow_lt_rpow_left_iff (by norm_num)]
      positivity
    _ = 2 := by norm_num
  