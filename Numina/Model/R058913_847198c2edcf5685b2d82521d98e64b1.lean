import Mathlib

theorem algebra_241018 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : a^2 + b^2 = 8) (h2 : a^6 + b^6 = 416) : a * b = 2 := by
  have h3 : a^6 + b^6 = (a^2 + b^2)^3 - 3 * (a^2 + b^2) * (a^2 * b^2) := by
    ring
  rw [h1] at h3
  rw [h3] at h2
  -- $8^3 = 512$, so $512 - 24 \cdot (a^2 b^2) = 416$
  -- rearranged gives $24 \cdot (a^2 b^2) = 96$, so $a^2 b^2 = 4$
  have h5 : a^2 * b^2 = 4 := by
    nlinarith
  have h4 : (a * b) ^ 2 = 4 := by
    nlinarith [sq_nonneg (a * b), h5]
  have h7 : a * b > 0 := by
    apply mul_pos
    exact ha
    exact hb
  have h8 : a * b = 2 := by
    nlinarith [h4, h7]
  exact h8