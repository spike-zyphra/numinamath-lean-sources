import Mathlib

theorem algebra_276238 {a b c : ℝ} (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (b - c) / ((a - b) * (a - c)) + (c - a) / ((b - c) * (b - a)) +
    (a - b) / ((c - a) * (c - b)) =
    2 / (a - b) + 2 / (b - c) + 2 / (c - a) := by
  rcases h with ⟨h1, h2, h3⟩
  have h4 : a - b ≠ 0 := by
    intro h'
    apply h1
    linarith
  have h5 : a - c ≠ 0 := by
    intro h'
    apply h2
    linarith
  have h6 : b - c ≠ 0 := by
    intro h'
    apply h3
    linarith
  have h7 : b - a ≠ 0 := by
    intro h'
    apply h1
    linarith
  have h8 : c - a ≠ 0 := by
    intro h'
    apply h2
    linarith
  have h9 : c - b ≠ 0 := by
    intro h'
    apply h3
    linarith
  -- now clear denominators
  field_simp [(show a - b ≠ 0 by exact h4), (show a - c ≠ 0 by exact h5), (show b - c ≠ 0 by exact h6), (show b - a ≠ 0 by exact h7), (show c - a ≠ 0 by exact h8), (show c - b ≠ 0 by exact h9)]
  ring