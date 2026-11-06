import Mathlib

theorem algebra_3340 : IsLeast {x : ℤ | x > Real.sqrt (7 + 2 * Real.sqrt 6) + Real.sqrt (7 - 2 * Real.sqrt 6)} 5 := by
  have h1 : Real.sqrt (7 + 2 * Real.sqrt 6) = Real.sqrt 6 + 1 := by
    have h2 : (Real.sqrt 6 + 1 : ℝ) ^ 2 = (7 + 2 * Real.sqrt 6 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    have h3 : Real.sqrt (7 + 2 * Real.sqrt 6 : ℝ) = Real.sqrt 6 + 1 := by
      rw [←h2]
      field_simp
      <;> nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (7 + 2 * Real.sqrt 6 : ℝ)]
    exact h3
  have h4 : Real.sqrt (7 - 2 * Real.sqrt 6) = Real.sqrt 6 - 1 := by
    have h5 : (Real.sqrt 6 - 1 : ℝ) ^ 2 = (7 - 2 * Real.sqrt 6 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    have h7 : Real.sqrt (7 - 2 * Real.sqrt 6 : ℝ) = Real.sqrt 6 - 1 := by
      have h8 : 0 ≤ (Real.sqrt 6 - 1 : ℝ) := by
        have h9 : Real.sqrt 6 ≥ Real.sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
        have h10 : Real.sqrt 1 = 1 := Real.sqrt_eq_cases.mpr (by norm_num)
        have h11 : Real.sqrt 6 ≥ (1 : ℝ) := by linarith [h9, h10]
        linarith
      have : Real.sqrt (7 - 2 * Real.sqrt 6 : ℝ) = Real.sqrt 6 - 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> (try norm_num) <;> nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), h8]
      exact this
    exact h7
  have h8 : Real.sqrt (7 + 2 * Real.sqrt 6 : ℝ) + Real.sqrt (7 - 2 * Real.sqrt 6 : ℝ) = 2 * Real.sqrt 6 := by
    rw [h1, h4]
    ring_nf
    <;> nlinarith [Real.sqrt_nonneg (6 : ℝ)]
  constructor
  · -- Show that 5 is indeed in the set.
    rw [Set.mem_setOf_eq]
    rw [h8]
    have h9 : (Real.sqrt 6 : ℝ) < (2.5 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), show (2.5 : ℝ) ^ 2 > (6 : ℝ) by norm_num]
    have h10 : (2 * Real.sqrt 6 : ℝ) < (5 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (6 : ℝ), h9]
    have h11 : (5 : ℤ) > (2 * Real.sqrt 6 : ℝ) := by
      exact_mod_cast h10
    exact_mod_cast h11
  · -- Show that 5 is the smallest integer in the set
    intro x hx
    rw [Set.mem_setOf_eq] at hx
    rw [h8] at hx
    by_contra h
    push_neg at h
    have h2 : (x : ℝ) ≤ (4 : ℝ) := by
      have h3 : x ≤ 4 := by
        omega
      exact_mod_cast h3
    have h4 : (2 * Real.sqrt 6 : ℝ) > (4 : ℝ) := by
      have h5 : (Real.sqrt 6 : ℝ) > (2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), show (2 : ℝ) ^ 2 < (6 : ℝ) by norm_num, Real.sqrt_nonneg (6 : ℝ)]
      nlinarith [h5, Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]