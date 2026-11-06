import Mathlib
theorem algebra_21305 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : c = 2 * Real.sqrt 6) (h₅ : a =  (Real.sin (Real.pi / 6)) * c) (h₆ : b =  Real.cos (Real.pi / 6) * c):
    a + b = Real.sqrt 6 + 3 * Real.sqrt 2 := by
  have h7 : Real.sin (Real.pi / 6) = 1 / 2 := by
    rw [Real.sin_pi_div_six]
  have h8 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := by 
    rw [Real.cos_pi_div_six]
  have ha1 : a = Real.sqrt 6 := by
    rw [h₅]
    rw [h7]
    rw [h₄]
    ring_nf
  have hb1 : b = Real.sqrt 3 * Real.sqrt 6 := by
    rw [h₆]
    rw [h8]
    rw [h₄]
    ring_nf
  have h10 : Real.sqrt 3 * Real.sqrt 6 = 3 * Real.sqrt 2 := by 
    have h11 : Real.sqrt 3 * Real.sqrt 6 = Real.sqrt 18 := by
      rw [← Real.sqrt_mul (by norm_num)]
      all_goals norm_num
    have h12 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf 
      <;> norm_num
    rw [h11, h12]
  rw [ha1, hb1, h10]
  <;> ring_nf