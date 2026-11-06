import Mathlib

open Real

theorem algebra_327829 {a : ℕ → ℝ} (ha1 : a 1 = 2)
    (han : ∀ n ≥ 1, a (n + 1) = (sqrt 2 - 1) * (a n + 2)) :
    ∀ n ≥ 1, a n = sqrt 2 * ((sqrt 2 - 1)^n + 1) := by
  intro n hn
  have h1 : ∀ (n : ℕ), a (n + 1) = sqrt 2 * ((sqrt 2 - 1) ^ (n + 1) + 1) := by
    intro n 
    induction n with 
    | zero =>
      rw [show (0 + 1 : ℕ) = 1 by rfl]
      rw [ha1]
      ring_nf
      <;> norm_num [pow_one, pow_two, pow_zero, mul_add, add_mul, mul_assoc]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    | succ n ih =>
      have h2 : a (n + 1) = sqrt 2 * ((sqrt 2 - 1) ^ (n + 1) + 1) := by
        simpa using ih
      have h3 : a (n + 1 + 1) = (sqrt 2 - 1) * (a (n + 1) + 2) := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [show n + 1 + 1 = (n + 2) by omega]
      rw [h3]
      rw [h2]
      have h4 : ((sqrt 2 - 1 : ℝ) ^ ((n + 1) + 1)) = ((sqrt 2 - 1) ^ (n + 1)) * (sqrt 2 - 1) := by
        ring_nf
      have h5 : (sqrt 2 * ((sqrt 2 - 1) ^ (n + 1) + 1)) + 2 = (sqrt 2 * ((sqrt 2 - 1) ^ (n + 1)) + sqrt 2) + 2 := by 
        ring_nf
      rw [h5]
      rw [h4]
      ring_nf 
      <;> norm_num [pow_two, Real.sq_sqrt, mul_add, add_mul, mul_sub, mul_assoc]
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  specialize h1 (n - 1)
  rw [show n - 1 + 1 = n by omega] at h1
  simpa using h1