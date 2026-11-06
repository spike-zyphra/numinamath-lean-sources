import Mathlib

theorem inequalities_598569 (x y z t α : ℝ) (h₀ : x ≥ y) (h₁ : y ≥ z) (h₂ : z ≥ t) (h₃ : t ≥ 0)
    (h₄ : y + z = 2 * α) :
    (x ^ 2 + y ^ 2) * (z ^ 2 + t ^ 2) ≤ (x ^ 2 + α ^ 2) * (α ^ 2 + t ^ 2) := by
  have h5 : α = (y + z) / 2 := by
    linarith
  rw [show α = (y + z) / 2 by linarith [h₄]]
  nlinarith [sq_nonneg (x - (y + z) / 2), sq_nonneg ((y + z) / 2 - z), sq_nonneg ((y + z) / 2 - y),
          sq_nonneg (z - t), sq_nonneg (y - z), sq_nonneg (x - y), sq_nonneg ((y + z) / 2 ^ 2 - z ^ 2),
          mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr h₁),
          mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂),
          mul_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr h₃),
          mul_nonneg (show (0 : ℝ) ≤ x by nlinarith) (show (0 : ℝ) ≤ t by linarith)
]