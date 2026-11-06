import Mathlib

open Real Set
open scoped Real

theorem algebra_289529 (x : ℝ) (hx : x = π/12) :
    sqrt (sin x ^ 4 + 4 * cos x ^ 2) - sqrt (cos x ^ 4 + 4 * sin x ^ 2) = sqrt 3 / 2 := by 
  have h1 : sin x ^ 4 + 4 * cos x ^ 2 = (1 + cos x ^ 2) ^ 2 := by 
    have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
    have h3 : sin x ^ 4 = (1 - cos x ^ 2) ^ 2 := by 
      calc 
        sin x ^ 4 = (sin x ^ 2) ^ 2 := by ring 
        _ = (1 - cos x ^ 2) ^ 2 := by 
          have : sin x ^ 2 = 1 - cos x ^ 2 := by linarith 
          rw [this] 
    nlinarith [h3] 
  have h1' : sqrt (sin x ^ 4 + 4 * cos x ^ 2) = 1 + cos x ^ 2 := by 
    rw [h1] 
    have h2 : 0 ≤ (1 + cos x ^ 2 : ℝ) := by 
      nlinarith [Real.cos_sq_add_sin_sq x, sq_nonneg (cos x)] 
    rw [Real.sqrt_sq (h2)] 
  have h4 : cos x ^ 4 + 4 * sin x ^ 2 = (cos x ^ 2 - 2) ^ 2 := by 
    have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
    have h5 : sin x ^ 2 = 1 - cos x ^ 2 := by linarith 
    nlinarith 
  have h4' : sqrt (cos x ^ 4 + 4 * sin x ^ 2) = 2 - cos x ^ 2 := by 
    rw [h4] 
    have h7 : sqrt ((cos x ^ 2 - 2) ^ 2) = abs (cos x ^ 2 - 2) := by 
      rw [Real.sqrt_sq_eq_abs] 
    rw [h7] 
    have h8 : cos x ^ 2 ≤ 1 := by 
      nlinarith [Real.cos_sq_add_sin_sq x, sq_nonneg (sin x)] 
    have h9 : cos x ^ 2 - 2 ≤ 0 := by 
      nlinarith 
    rw [abs_of_nonpos h9] 
    all_goals nlinarith 
  rw [h1', h4'] 
  have h6 : cos x ^ 2 = (2 + Real.sqrt 3) / 4 := by 
    have h7 : x = Real.pi / 12 := by 
      linarith 
    rw [h7] 
    have h8 : cos (Real.pi / 12) ^ 2 = (2 + Real.sqrt 3) / 4 := by 
      have h9 : cos (Real.pi / 12) ^ 2 = (1 + Real.cos (2 * (Real.pi / 12))) / 2 := by 
        rw [cos_sq] 
        <;> ring 
      have h10 : 2 * (Real.pi / 12) = Real.pi / 6 := by 
        ring 
      rw [h10] at h9 
      have h11 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by 
        exact cos_pi_div_six 
      rw [h11] at h9 
      linarith 
    linarith [h8] 
  nlinarith [h6, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]