import Mathlib

theorem inequalities_265987 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ≤ b ∧ b ≤ c) :
    (-a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 3 := by
  rcases h with ⟨h1, h2⟩
  have h3 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h4 : (-a + b + c) * (1 / a + 1 / b + 1 / c) - 3 ≥ 0 := by
    have pos1 : 0 < a * b * c := h3
    have eq : (-a + b + c) * (1 / a + 1 / b + 1 / c) - 3 =
        ((-a + b + c) * (a * b + a * c + b * c) - 3 * (a * b * c)) / (a * b * c) := by
      field_simp
      <;> ring
    rw [eq]
    apply div_nonneg
    have h5 : (-a + b + c) * (a * b + a * c + b * c) - 3 * (a * b * c) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * b - a * c), sq_nonneg (b * a - b * c), sq_nonneg (a * c - b * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - b by linarith),
        mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - a by linarith),
        mul_nonneg (show 0 ≤ c - b by linarith) (show 0 ≤ c - a by linarith)]
    linarith [h5]
    positivity
  linarith [h4]