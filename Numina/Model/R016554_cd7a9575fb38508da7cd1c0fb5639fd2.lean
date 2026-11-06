import Mathlib

theorem calculus_181396 (f : ℝ → ℝ) (hf : f = fun x => x^3 * Real.exp (-x)) :
    f 3 = 27 / Real.exp 3 := by 
  rw [hf]
  have h1 : (3 : ℝ) ^ 3 * Real.exp (- (3 : ℝ)) = 27 / Real.exp (3 : ℝ) := by
    have h2 : Real.exp (- (3 : ℝ)) = (Real.exp (3 : ℝ))⁻¹ := by
      rw [show - (3 : ℝ) = - (3 : ℝ) by rfl]
      rw [Real.exp_neg]
    rw [h2]
    field_simp
    <;> ring_nf
  simp [h1]
  all_goals linarith