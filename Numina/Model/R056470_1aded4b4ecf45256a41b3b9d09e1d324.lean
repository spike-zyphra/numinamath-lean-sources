import Mathlib

theorem algebra_178656 {a b c x : ℝ} (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    c * ((x - a) * (x - b)) / ((c - a) * (c - b)) +
    b * ((x - a) * (x - c)) / ((b - a) * (b - c)) +
    a * ((x - b) * (x - c)) / ((a - b) * (a - c)) = x := by 
  have h1 : a ≠ b := h.1
  have h2 : a ≠ c := h.2.1
  have h3 : b ≠ c := h.2.2
  have h4 : c - a ≠ 0 := by intro h'; apply h2; linarith
  have h5 : c - b ≠ 0 := by intro h'; apply h3; linarith
  have h6 : b - a ≠ 0 := by intro h'; apply h1; linarith
  have h7 : b - c ≠ 0 := by intro h'; apply h3; linarith
  have h8 : a - b ≠ 0 := by intro h'; apply h1; linarith
  have h9 : a - c ≠ 0 := by intro h'; apply h2; linarith 
  field_simp [(show c - a ≠ 0 by exact h4), 
    (show c - b ≠ 0 by exact h5), 
    (show b - a ≠ 0 by exact h6), 
    (show b - c ≠ 0 by exact h7), 
    (show a - b ≠ 0 by exact h8), 
    (show a - c ≠ 0 by exact h9)]
  ring