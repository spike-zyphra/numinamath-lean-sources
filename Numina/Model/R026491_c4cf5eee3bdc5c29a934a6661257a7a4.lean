import Mathlib

theorem algebra_9402 {a b c : ℝ} (h : a + b ≠ 0 ∧ b + c ≠ 0 ∧ c + a ≠ 0 ∧ (a - b) * (b - c) * (c - a) / ((a + b) * (b + c) * (c + a)) = 2004 / 2005) :
    a / (a + b) + b / (b + c) + c / (c + a) = 4011 / 4010 := by
  rcases h with ⟨h1, h2, h3, heq⟩
  have h4 : a + b ≠ 0 := h1
  have h5 : b + c ≠ 0 := h2
  have h6 : c + a ≠ 0 := h3

  have h7 : a / (a + b) + b / (b + c) + c / (c + a) =
      (a * (b + c) * (c + a) + b * (a + b) * (c + a) + c * (a + b) * (b + c)) / ((a + b) * (b + c) * (c + a)) := by
    field_simp [h1, h2, h3]
    <;> ring

  rw [h7]
  have h8 : (a * (b + c) * (c + a) + b * (a + b) * (c + a) + c * (a + b) * (b + c)) =
      (3 / 2) * (a + b) * (b + c) * (c + a) - (1 / 2) * (a - b) * (b - c) * (c - a) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)]

  have h9 : (a * (b + c) * (c + a) + b * (a + b) * (c + a) + c * (a + b) * (b + c)) / ((a + b) * (b + c) * (c + a)) =
    (3 / 2) - (1 / 2) * ((a - b) * (b - c) * (c - a) / ((a + b) * (b + c) * (c + a))) := by
    rw [h8]
    field_simp [h1, h2, h3]
    <;> ring

  rw [h9]
  have heq3 : (a - b) * (b - c) * (c - a) / ((a + b) * (b + c) * (c + a)) = 2004 / 2005 := heq
  rw [heq3]
  norm_num