import Mathlib

theorem algebra_178501 {h a r v d m i t : ℝ}
    (h₀ : h * a * r * v * a * r * d = 100) (h₁ : h * m * m * t = 100)
    (h₂ : m * i * t = 100) :
    (r * a * d) * (t * r * i * v * i * a) = 10000 := by
  -- First, rewrite h₀ as h * a^2 * r^2 * v * d = 100 for clarity.
  have eq1 : h * a^2 * r^2 * v * d = 100 := by
    ring_nf at h₀ ⊢
    linarith

  have eq2 : m * i * t = 100 := h₂

  -- Multiply eq1 by eq2 to get h * a^2 * r^2 * v * d * (m * i * t) = 10000
  have h3 : h * a^2 * r^2 * v * d * (m * i * t) = 10000 := by
    calc
      h * a^2 * r^2 * v * d * (m * i * t) = (h * a^2 * r^2 * v * d) * (m * i * t) := by ring
      _ = 100 * 100 := by
        rw [eq1, eq2]
      _ = 10000 := by norm_num

  -- Rewrite the target expression.
  have h4 : (r * a * d) * (t * r * i * v * i * a) = r^2 * a^2 * d * t * i^2 * v := by
    ring

  rw [h4]

  -- Use h3 to express the result
  nlinarith [sq_nonneg (h * m - 1), sq_nonneg (i - h * m), sq_nonneg (a * r), sq_nonneg (v * d), sq_nonneg (m * t), h₁, h₂, h₀, sq_pos_of_pos (show (100 : ℝ) > 0 by norm_num)]