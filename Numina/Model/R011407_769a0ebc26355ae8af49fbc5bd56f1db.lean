import Mathlib

open Real
theorem algebra_251156:
0 ≤ 1 + 3 * (sin x)^3 ∧ 
0 ≤ 1 - (cos x)^4 ∧ 
sqrt (1 + 3 * (sin x)^3) = 3 - sqrt (1 - (cos x)^4) 
↔ 
(∃ k:ℤ, π/2 + k * (2 * π) = x) := by
  constructor
  · -- Forward implication: if the equation holds, then prove x = π/2 + k*(2*π)
    rintro ⟨h1, h2, heq⟩
    have h3 : (sqrt (1 + 3 * (sin x) ^ 3)) ^ 2 = (3 - sqrt (1 - (cos x) ^ 4)) ^ 2 := by
      rw [heq]
    have h4 : (sqrt (1 + 3 * (sin x) ^ 3)) ^ 2 = 1 + 3 * (sin x) ^ 3 := by
      apply Real.sq_sqrt
      linarith
    have h5 : (sqrt (1 - (cos x) ^ 4)) ^ 2 = 1 - (cos x) ^ 4 := by
      apply Real.sq_sqrt
      linarith
    have eq1 : 1 + 3 * (sin x) ^ 3 = 9 - 6 * (sqrt (1 - (cos x) ^ 4)) + (1 - (cos x) ^ 4) := by
      nlinarith [h3, h4, h5]
    have h6 : sin x = 1 := by
      have h7 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      have h9 : sqrt (1 - (cos x) ^ 4) ≥ 0 := Real.sqrt_nonneg (1 - (cos x) ^ 4)
      have eq2 : sin x ≥ -1 := by
        nlinarith [sq_nonneg (sin x + 1), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x, h9]
      have eq3 : sin x ≤ 1 := by
        nlinarith [sq_nonneg (sin x - 1), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x, h9]
      nlinarith [sq_nonneg (sin x - 1), sq_nonneg (cos x ^ 2 - 0), sq_nonneg (sqrt (1 - (cos x) ^ 4) - 1), 
        sq_nonneg (sin x ^ 2 - 1), Real.sqrt_nonneg (1 + 3 * (sin x) ^ 3), 
        Real.sqrt_nonneg (1 - (cos x) ^ 4), 
        mul_nonneg (Real.sqrt_nonneg (1 + 3 * (sin x) ^ 3)) (Real.sqrt_nonneg (1 - (cos x) ^ 4)), 
        sq_nonneg (sin x), 
        sq_nonneg (cos x ^ 2), 
        pow_two_nonneg (sin x - 1), 
        pow_two_nonneg (cos x ^ 2 - 0)
      ]
    -- From sin x = 1, we deduce cos x = 0
    have h7 : cos x = 0 := by
      have h8 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      rw [h6] at h8
      nlinarith
    -- Now we prove the existence of k
    have h8 : ∃ k:ℤ, π/2 + k * (2 * π) = x := by
      have h11 : sin x = 1 := h6
      obtain ⟨k, hk⟩ := Real.sin_eq_one_iff.1 h11
      refine ⟨k, by linarith [hk]⟩
    tauto
  · -- Backward implication: if x = π/2 + k * (2*π), prove the equation
    rintro ⟨k, hk⟩
    have h10 : x = π / 2 + (k : ℝ) * (2 * π) := by
      linarith [hk]
    have h11 : sin x = 1 := by
      rw [show x = π / 2 + (k : ℝ) * (2 * π) by linarith [hk]]
      have : π / 2 + (k : ℝ) * (2 * π) = π / 2 + (k : ℝ) * (2 * π) := by rfl
      have h19 : sin (π / 2 + (k : ℝ) * (2 * π)) = sin (π / 2) := by
        rw [show π / 2 + (k : ℝ) * (2 * π) = π / 2 + ↑k * (2 * π) by ring]
        rw [sin_add_int_mul_two_pi (π / 2) k]
      have h18 : sin (π / 2) = 1 := Real.sin_pi_div_two
      linarith [h19, h18]
    have h12 : cos x = 0 := by
      rw [show x = π / 2 + (k : ℝ) * (2 * π) by linarith [hk]]
      have : π / 2 + (k : ℝ) * (2 * π) = π / 2 + (k : ℝ) * (2 * π) := by rfl
      have h19 : cos (π / 2 + (k : ℝ) * (2 * π)) = cos (π / 2) := by
        rw [show π / 2 + (k : ℝ) * (2 * π) = π / 2 + ↑k * (2 * π) by ring]
        rw [cos_add_int_mul_two_pi (π / 2) k]
      have h18 : cos (π / 2) = 0 := Real.cos_pi_div_two
      linarith [h19, h18]
    constructor
    · -- Show 0 ≤ 1 + 3 * (sin x)^3
      rw [show sin x = 1 by linarith [h11]]
      norm_num
    constructor
    · -- Show 0 ≤ 1 - (cos x)^4
      rw [show cos x = 0 by linarith [h12]]
      norm_num
    · -- Show sqrt (1 + 3 * (sin x)^3) = 3 - sqrt (1 - (cos x)^4)
      have h13 : sqrt (1 + 3 * (sin x) ^ 3) = 2 := by
        rw [show sin x = 1 by linarith [h11]]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h14 : sqrt (1 - (cos x) ^ 4) = 1 := by
        rw [show cos x = 0 by linarith [h12]]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h13, h14]
      all_goals norm_num