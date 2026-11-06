import Mathlib

/-
The positive numbers $a, b$ and $c$ satisfy $a  \ge  b \ge c$ and $a + b + c \le 1$ . Prove that $a^2 + 3b^2 + 5c^2 \le 1$ . 
-/
theorem inequalities_66734 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a ≥ b ∧ b ≥ c) (h2 : a + b + c ≤ 1) :
    a^2 + 3 * b^2 + 5 * c^2 ≤ 1 := by
  -- Two steps:
  -- 1. Show that LHS ≤ (a + b + c) ^ 2
  -- 2. Use (a + b + c) ^ 2 ≤ 1, which is trivial
  have h3 : a ^ 2 + 3 * b ^ 2 + 5 * c ^ 2 ≤ (a + b + c) ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
              sq_nonneg (a + b - 2 * c)]
  have h4 : (a + b + c) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (a + b + c - 1), h2]
  nlinarith [h3, h4]