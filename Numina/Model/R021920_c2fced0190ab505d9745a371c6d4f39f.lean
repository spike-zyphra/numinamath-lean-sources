import Mathlib

theorem algebra_327367 {a b c : ℝ} (h₀ : a ≠ 0) (h₁ : b ≠ 0) (h₂ : c ≠ 0)
    (h₃ : a + b + c = a * b * c) :
    (1 - a^2) * (1 - b^2) / (a * b) + (1 - b^2) * (1 - c^2) / (b * c) +
    (1 - c^2) * (1 - a^2) / (a * c) = 4 := by 
  have eq1 : (1 - a^2) * (1 - b^2) / (a * b) + (1 - b^2) * (1 - c^2) / (b * c) + (1 - c^2) * (1 - a^2) / (a * c) =
      ( (1 - a^2) * (1 - b^2) * c + (1 - b^2) * (1 - c^2) * a + (1 - c^2) * (1 - a^2) * b ) / (a * b * c) := by
    field_simp [h₀, h₁, h₂]
    ring
  rw [eq1]
  have eq2 : ( (1 - a^2) * (1 - b^2) * c + (1 - b^2) * (1 - c^2) * a + (1 - c^2) * (1 - a^2) * b ) = 4 * (a * b * c) := by
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1),
          sq_nonneg (a + b + c - a * b * c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          h₃, sq_pos_of_ne_zero (show a * b * c ≠ 0 by
            apply mul_ne_zero
            apply mul_ne_zero
            exact h₀
            exact h₁
            exact h₂
          )
        ]
  rw [eq2]
  field_simp [h₃, h₀, h₁, h₂]
  <;> nlinarith
  <;> nlinarith