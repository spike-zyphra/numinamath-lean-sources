import Mathlib

theorem algebra_168803 {a b c : ℝ} (ha : a ≠ -b) (hb : b ≠ -c) (hc : a ≠ -c)
    (h : ∃ d, 1 / (a + b) = 1 / (a + c) + d ∧ 1 / (a + c) = 1 / (b + c) + d) :
    ∃ d, b ^ 2 = a ^ 2 + d ∧ c ^ 2 = b ^ 2 + d := by
  rcases h with ⟨d, h1, h2⟩
  have h3 : a + b ≠ 0 := by
    intro h'
    apply ha
    linarith
  have h4 : a + c ≠ 0 := by
    intro h'
    apply hc
    linarith
  have h5 : b + c ≠ 0 := by
    intro h'
    apply hb
    linarith
  have eq1 : 1 / (a + b) - 1 / (a + c) = d := by linarith
  have eq2 : 1 / (a + c) - 1 / (b + c) = d := by linarith
  have eq3 : 1 / (a + b) - 1 / (a + c) = 1 / (a + c) - 1 / (b + c) := by
    linarith [eq1, eq2]
  have eq4 : (c - b) * (b + c) = (b - a) * (a + b) := by
    have eq6 : 1 / (a + b) - 1 / (a + c) = 1 / (a + c) - 1 / (b + c) := by
      linarith [eq1, eq2]
    have eq7 : (1 / (a + b) - 1 / (a + c)) * ((a + b) * (a + c) * (b + c)) = (1 / (a + c) - 1 / (b + c)) * ((a + b) * (a + c) * (b + c)) := by
      rw [eq6]
    have eq8 : (1 / (a + b) - 1 / (a + c)) * ((a + b) * (a + c) * (b + c)) = (c - b) * (b + c) := by
      have h7 : a + b ≠ 0 := h3
      have h8 : a + c ≠ 0 := h4
      have h9 : b + c ≠ 0 := h5
      field_simp [h7, h8, h9]
      <;> ring
    have eq9 : (1 / (a + c) - 1 / (b + c)) * ((a + b) * (a + c) * (b + c)) = (b - a) * (a + b) := by
      have h7 : a + c ≠ 0 := h4
      have h8 : b + c ≠ 0 := h5
      have h9 : a + b ≠ 0 := h3
      field_simp [h7, h8, h9]
      <;> ring
    rw [eq8] at eq7
    rw [eq9] at eq7
    linarith
  have eq5 : 2 * b ^ 2 = a ^ 2 + c ^ 2 := by
    have eq7 : (c - b) * (b + c) = (b - a) * (a + b) := eq4
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
      sq_pos_of_ne_zero (show a + b ≠ 0 by exact h3), 
      sq_pos_of_ne_zero (show a + c ≠ 0 by exact h4),
      sq_pos_of_ne_zero (show b + c ≠ 0 by exact h5)
    ]
  use (b ^ 2 - a ^ 2)
  constructor
  · -- Show b ^ 2 = a ^ 2 + d 
    nlinarith [eq5]
  · -- Show c ^ 2 = b ^ 2 + d 
    nlinarith [eq5]