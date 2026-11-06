import Mathlib

/- If \[\frac{x}{y} = \frac{4}{5}, \; \frac{y}{z} = \frac{3}{10}, \;\text{and} \; \frac{z}{w} = \frac{6}{7},\] what is the value of $\dfrac{x + y + w}{z}$? Express your answer as a common fraction. -/
theorem algebra_20644 {x y z w : ℝ} (h₀ : x / y = 4 / 5) (h₁ : y / z = 3 / 10)
    (h₂ : z / w = 6 / 7) : (x + y + w) / z = 128 / 75 := by
  have h₃ : y ≠ 0 := by rintro rfl; norm_num at h₀
  have h₄ : z ≠ 0 := by rintro rfl; norm_num at h₁
  have h₅ : w ≠ 0 := by rintro rfl; norm_num at h₂
  field_simp at *
  linarith