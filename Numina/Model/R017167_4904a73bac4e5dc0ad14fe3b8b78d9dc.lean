import Mathlib

theorem inequalities_292479 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a^2 + b^2 + c^2 + d^2 = 4) :
    ∃ x y, (x = a ∧ y = b) ∨ (x = a ∧ y = c) ∨ (x = a ∧ y = d) ∨ (x = b ∧ y = c) ∨
    (x = b ∧ y = d) ∨ (x = c ∧ y = d) ∧ x + y ≤ 2 := by

  by_cases h1 : a ≤ b ∧ a ≤ c ∧ a ≤ d
  · -- If a is the minimum
    use a, b
    simp
    all_goals nlinarith
  by_cases h2 : b ≤ a ∧ b ≤ c ∧ b ≤ d
  · -- If b is the minimum
    use a, b
    simp
    all_goals nlinarith
  by_cases h3 : c ≤ a ∧ c ≤ b ∧ c ≤ d
  · -- If c is the minimum
    use a, c
    simp
    all_goals nlinarith
  · -- else, d is the minimum
    use a, d
    simp
    all_goals nlinarith