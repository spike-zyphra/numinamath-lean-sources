import Mathlib

open Real Set

theorem inequalities_232822 (A B : ℝ) (hA : A ∈ Icc 0 Real.pi) (hB : B ∈ Icc 0 Real.pi) :
    |sin A - sin B| ≤ |sin (A - B)| := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  have h9 : sin A ≥ 0 := by apply sin_nonneg_of_nonneg_of_le_pi; linarith; linarith
  have h10 : sin B ≥ 0 := by apply sin_nonneg_of_nonneg_of_le_pi; linarith; linarith
  have h3 : sin (A - B) = sin A * cos B - cos A * sin B := by 
    rw [sin_sub]
  have h11 : cos A ≤ 1 := by 
    apply cos_le_one
  have h12 : cos B ≤ 1 := by 
    apply cos_le_one
  have h13 : -1 ≤ cos A := by 
    apply neg_one_le_cos
  have h14 : -1 ≤ cos B := by 
    apply neg_one_le_cos
  have h15 : (sin A - sin B : ℝ) ^ 2 ≤ (sin (A - B) : ℝ) ^ 2 := by
    rw [h3]
    nlinarith [sq_nonneg (sin A - sin B), sq_nonneg (sin A * cos B - cos A * sin B), 
      sq_nonneg (cos A - cos B), sq_nonneg (sin A - sin B), 
      sq_nonneg (A - B), Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, 
      mul_nonneg (show 0 ≤ sin A by linarith) (show 0 ≤ sin B by linarith), 
      sq_nonneg (cos A + cos B), 
      sq_nonneg (sin A - sin B), 
      mul_nonneg (show 0 ≤ sin A by linarith) (show 0 ≤ 1 - cos B by nlinarith [Real.sin_sq_add_cos_sq B, Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ B by linarith) (show B ≤ Real.pi by linarith)]), 
      mul_nonneg (show 0 ≤ sin B by linarith) (show 0 ≤ 1 - cos A by nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ A by linarith) (show A ≤ Real.pi by linarith)])
    ]
  have h16 : |sin A - sin B| ≤ |sin (A - B)| := by 
    apply sq_le_sq.mp 
    simp [abs_le] at *
    all_goals nlinarith [h15, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq (A - B)]
  exact h16