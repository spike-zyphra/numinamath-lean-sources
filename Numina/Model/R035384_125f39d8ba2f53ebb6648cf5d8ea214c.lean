import Mathlib

theorem algebra_256614 {a b c : ℝ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) :
    (a / b + b / a) ^ 2 + (b / c + c / b) ^ 2 + (c / a + a / c) ^ 2 =
    4 + (a / b + b / a) * (b / c + c / b) * (c / a + a / c) := by

  rcases habc with ⟨ha, hb, hc⟩
  field_simp [ha, hb, hc]
  ring