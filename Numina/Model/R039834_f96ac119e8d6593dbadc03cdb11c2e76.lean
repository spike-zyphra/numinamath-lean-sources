import Mathlib

theorem inequalities_597058 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = 1) :
    (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by
  have h1 : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) = ((a * b - b + 1) * (b * c - c + 1) * (c * a - a + 1)) / (a * b * c) := by
    field_simp
    ring

  rw [h1]

  have h3 : ((a * b - b + 1) * (b * c - c + 1) * (c * a - a + 1)) ≤ 1 := by
    nlinarith [sq_nonneg (a * b - b + 1 - 1), sq_nonneg (b * c - c + 1 - 1), sq_nonneg (c * a - a + 1 - 1),
        sq_nonneg (a * b * c - 1), mul_nonneg (show 0 ≤ a * b by positivity) (show 0 ≤ b * c by positivity),
        mul_nonneg (show 0 ≤ b * c by positivity) (show 0 ≤ c * a by positivity),
        mul_nonneg (show 0 ≤ c * a by positivity) (show 0 ≤ a * b by positivity),
        mul_nonneg (show 0 ≤ b by positivity) (show 0 ≤ c by positivity),
        mul_nonneg (show 0 ≤ c by positivity) (show 0 ≤ a by positivity),
        mul_nonneg (show 0 ≤ a by positivity) (show 0 ≤ b by positivity),
        sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a + b + c - 3)]

  have h5 : ((a * b - b + 1) * (b * c - c + 1) * (c * a - a + 1)) / (a * b * c) ≤ 1 := by
    have h11 : a * b * c > 0 := by
      positivity

    have h13 : ((a * b - b + 1) * (b * c - c + 1) * (c * a - a + 1)) ≤ 1 := h3

    have h14 : ((a * b - b + 1) * (b * c - c + 1) * (c * a - a + 1)) / (a * b * c) ≤ (1 : ℝ) := by
      have h111 : a * b * c > 0 := by positivity
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith

    linarith

  linarith