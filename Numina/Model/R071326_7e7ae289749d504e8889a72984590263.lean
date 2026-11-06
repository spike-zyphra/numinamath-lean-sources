import Mathlib

theorem algebra_4609
    (a b : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (h1 : 1 / a + 1 / b = 1 / 8)
    (h2 : 6 * a + 12 * b = 34800 / 1000)
    (h3 : 12 * a + 6 * b = 35200 / 1000) :
    a = 36000 ∧ b = 33600 := by
  have h1' : a * b = 8 * (a + b) := by
    field_simp at h1
    nlinarith
  nlinarith [sq_nonneg (a - 36000), sq_nonneg (b - 33600),
            mul_pos ha hb]