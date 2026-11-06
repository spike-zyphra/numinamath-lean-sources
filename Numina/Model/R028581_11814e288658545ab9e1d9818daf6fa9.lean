import Mathlib
open Real

theorem algebra_9300 {f : ℝ → ℝ} (hf : ∀ x, f x = deriv f (π / 4) * cos x + sin x) :
    f (π / 4) = 1 := by
  let y := deriv f (π / 4)
  have h1 : f (π / 4) = y * cos (π / 4) + sin (π / 4) := by
    specialize hf (π / 4)
    simpa using hf

  have eq1 : deriv f (π / 4) = -y * sin (π / 4) + cos (π / 4) := by
    have eq2 : f = fun x => y * cos x + sin x := by
      funext x
      specialize hf x
      simpa using hf
    rw [eq2]
    simp [deriv_add, deriv_mul, deriv_id'', mul_comm y, differentiableAt_cos]
    <;> field_simp <;> ring

  have h2 : cos (π / 4) = Real.sqrt 2 / 2 := by 
    rw [cos_pi_div_four]

  have h3 : sin (π / 4) = Real.sqrt 2 / 2 := by 
    rw [sin_pi_div_four]

  rw [h2, h3] at eq1
  rw [h2, h3] at h1

  have eq3 : y = Real.sqrt 2 - 1 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (y - (Real.sqrt 2 - 1)), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]
  
  rw [eq3] at h1
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), sq_nonneg (Real.sqrt 2 ^ 2 - 2)]