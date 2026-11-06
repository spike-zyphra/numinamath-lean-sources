import Mathlib

open Real Set
open scoped Real

theorem algebra_600799 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ π/2) :
    1 / sqrt 2 ≤ (sin x)^3 + (cos x)^3 ∧ (sin x)^3 + (cos x)^3 ≤ 1 := by
  rcases hx with ⟨hx1, hx2⟩
  have h3 : sin x ≥ 0 := by 
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos, hx2]
  have h4 : cos x ≥ 0 := by 
    have h2' : x ≤ π / 2 := hx2 
    have h5 : cos x ≥ 0 := by 
      apply cos_nonneg_of_mem_Icc 
      constructor 
      linarith [Real.pi_pos, h2']
      linarith [Real.pi_pos, h2']
    linarith 
  have h7 : sin x ≤ 1 := by 
    have h8 : sin x ≤ 1 := Real.sin_le_one x 
    linarith 
  have h8' : cos x ≤ 1 := by 
    have h8 : cos x ≤ 1 := Real.cos_le_one x 
    linarith 
  have h10 : (sin x) ^ 2 + (cos x) ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
  have h11 : 1 / sqrt 2 ≤ (sin x)^3 + (cos x)^3 := by
    have h100 : 1 / sqrt 2 = sqrt 2 / 2 := by 
      field_simp [Real.sqrt_ne_zero']
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)]
    rw [h100]
    have h9' : (sin x) ^ 3 + (cos x) ^ 3 ≥ sqrt 2 / 2 := by 
      nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x - sqrt 2), sq_nonneg (sin x - sqrt 2 / 2), sq_nonneg (cos x - sqrt 2 / 2), 
          h3, h4, h7, h8', 
          mul_nonneg h3 h4, 
          Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith), 
          sq_nonneg (sin x * cos x - (sqrt 2 / 2) * (sqrt 2 / 2) / 2), 
          Real.sin_sq_add_cos_sq x 
        ]
    linarith
  have h12 : (sin x) ^ 3 + (cos x) ^ 3 ≤ 1 := by 
    nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x - 1), sq_nonneg (x - π / 2), sq_nonneg (x - 0), 
        h3, h4, h7, h8', 
        mul_nonneg h3 h4, 
        Real.sin_sq_add_cos_sq x 
      ]
  constructor
  · -- Prove the lower bound
    linarith [h11]
  · -- Prove the upper bound
    linarith [h12]