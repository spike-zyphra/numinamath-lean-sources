import Mathlib

theorem algebra_13412 (f : ℝ → ℝ) (hf : 2 * f = λx ↦ -3 * x + 6) :
    deriv f 1 = -3 / 2 := by
  have hf : f =  λx ↦ (-3/2) * x + 3 := by
    have : (λx ↦ (-3/2) * x + 3) = (2 * f) / 2 := by
      rw [hf]
      funext x
      field_simp; norm_num
    rw [this]
    ext x
    simp
  rw [hf]
  simp only [mul_comm]
  norm_num
