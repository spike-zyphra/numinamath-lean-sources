import Mathlib

/- If $\tan \alpha = 1$, then the value of $\frac{2\sin^{2}\alpha + 1}{\sin 2\alpha}$ is ______. -/
theorem algebra_533152 (α : ℝ) (h : Real.tan α = 1) :
    (2 * (Real.sin α)^2 + 1) / (Real.sin (2 * α)) = 2 := by 
  rw [Real.tan_eq_sin_div_cos] at h
  have h1 : Real.sin α ≠ 0 := by
    intro h2
    rw [h2] at h
    norm_num at h
  have h2 : Real.cos α ≠ 0 := by
    intro h3
    rw [h3] at h
    norm_num at h
  field_simp [Real.sin_two_mul] at *
  rw [← sub_eq_zero] at h
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_le_one α, Real.cos_le_one α]
