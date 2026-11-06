import Mathlib
open Real

lemma lemma_1 : sin (π/18) ≠ 0 := by
  · rw [sin_ne_zero_iff]
    intro n
    ring_nf
    rw [mul_comm]
    simp only [one_div, ne_eq, mul_eq_mul_left_iff, not_or]
    push_neg
    constructor
    . by_contra! hc₀
      have hc₁: 18 * (n : ℝ) = 1 := by
        rw [mul_comm]
        exact (mul_eq_one_iff_eq_inv₀ (by norm_num)).mpr hc₀
      norm_cast at hc₁
      have g₀: 0 < n := by linarith
      linarith
    . exact pi_ne_zero

theorem algebra_178443 : cot (π/18) - 4 * cos (π/18) = √3 := by
  have h1 : cot (π / 18) = cos (π / 18) / sin (π / 18) := by 
    rw [cot_eq_cos_div_sin]
  rw [h1]
  have h2 : sin (π / 18) ≠ 0 := lemma_1
  have eq1 : cos (π / 18) / sin (π / 18) - 4 * cos (π / 18) = (cos (π / 18) - 4 * cos (π / 18) * sin (π / 18)) / sin (π / 18) := by
    field_simp [h2]
    <;> ring
  rw [eq1] at *
  have eq2 : cos (π / 18) - 4 * cos (π / 18) * sin (π / 18) = Real.sqrt 3 * sin (π / 18) := by
    have h3 : cos (π / 18) - 4 * cos (π / 18) * sin (π / 18) = cos (π / 18) - 2 * (2 * cos (π / 18) * sin (π / 18)) := by ring
    have h4 : 2 * cos (π / 18) * sin (π / 18) = sin (2 * (π / 18)) := by
      rw [sin_two_mul]
      all_goals ring
    have h5 : sin (2 * (π / 18)) = sin (π / 9) := by ring_nf
    have h6 : sin (π / 9) = sin (Real.pi / 6 - π / 18) := by ring_nf
    have h7 : sin (Real.pi / 6 - π / 18) = sin (Real.pi / 6) * cos (π / 18) - cos (Real.pi / 6) * sin (π / 18) := by
      rw [sin_sub]
    have h8 : sin (Real.pi / 6) = 1 / 2 := by 
      exact sin_pi_div_six
    have h9 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by 
      have h1 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
        exact cos_pi_div_six
      linarith
    rw [h3, h4, h5, h6, h7, h8, h9]
    ring
  have eq3 : (cos (π / 18) - 4 * cos (π / 18) * sin (π / 18)) / sin (π / 18) = Real.sqrt 3 := by 
    have h2' : sin (π / 18) ≠ 0 := h2
    field_simp [h2']
    all_goals linarith [eq2]
  linarith [eq3]