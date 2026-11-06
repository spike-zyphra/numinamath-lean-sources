import Mathlib

  theorem algebra_181930 {a b : ℕ} (h₂ : 1 ≤ a ∧ a ≤ 9) (h₃ :  1 ≤ b ∧ b ≤ 9 )
    (hn : a + b = 9) (h₃ : 5 * (10 * a + b) - 9 = 10 * b + a) :
    10 * a + b = 18 := by
  have h21 : 1 ≤ a := h₂.1
  have h22 : a ≤ 9 := h₂.2
  -- Rewrite subtraction using omega
  have eq2 : 5 * (10 * a + b) = (10 * b + a) + 9 := by
    omega
  have eq1 : a + b = 9 := hn
  -- Using omega to solve from equalities eq1 and eq2.
  omega