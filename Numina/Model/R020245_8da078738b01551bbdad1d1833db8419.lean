import Mathlib

theorem number_theory_238131 : ¬∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a * b = 2 * c * d ∧ a * b * c * d = 100 := by
  rintro ⟨a, b, c, d, ha, hb, hc, hd, h1, he⟩
  have heq1 : a * b * c * d = 100 := he
  have heq2 : a * b = 2 * c * d := h1
  have heq4 : (a * b) * (c * d) = 100 := by
    calc
      (a * b) * (c * d) = a * b * c * d := by ring
      _ = 100 := he
  have heq5 : a * b = 2 * c * d := h1
  have heq8 : (a * b) * (c * d) = 2 * (c * d) * (c * d) := by 
    have h_eq : (a * b) * (c * d) = 2 * (c * d) * (c * d) := by 
      calc 
        (a * b) * (c * d) = (2 * c * d) * (c * d) := by 
          rw [show a * b = 2 * c * d by linarith]
        _ = 2 * (c * d) * (c * d) := by ring 
    linarith [h_eq]
  have heq9 : 2 * (c * d) * (c * d) = 100 := by 
    nlinarith [heq4, heq8]
  have heq10 : (c * d) * (c * d) = 50 := by 
    nlinarith [heq9]
  have heq11 : (c * d) ≤ 7 := by 
    nlinarith [sq_nonneg (c * d), heq10]
  have heq12 : (c * d) * (c * d) = 50 := heq10
  interval_cases h : (c * d) <;> omega