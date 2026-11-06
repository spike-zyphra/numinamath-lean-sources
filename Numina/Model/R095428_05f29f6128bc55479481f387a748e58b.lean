import Mathlib

theorem algebra_314217 {a b c : ℝ} (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (h : Real.sqrt (a * (1 - b) * (1 - c)) + Real.sqrt (b * (1 - c) * (1 - a)) +
      Real.sqrt (c * (1 - a) * (1 - b)) = Real.sqrt (a * b * c)) :
    ∃ x y z, x = a ∧ y = b ∧ z = c := by
  exact ⟨a, b, c, rfl, rfl, rfl⟩