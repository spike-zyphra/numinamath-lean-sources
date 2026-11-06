import Mathlib

theorem algebra_2196 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
  (h : (1 / b : ℚ) * 3 + (1 / a + 1 / b : ℚ) * 1 = 1) :
  a + b = 10 ∨ a + b = 9 := by
  have h1 : (a : ℚ) > 0 := by exact_mod_cast ha
  have h2 : (b : ℚ) > 0 := by exact_mod_cast hb
  have eq1 : (a : ℚ) * (b : ℚ) = 4 * (a : ℚ) + (b : ℚ) := by
    have eq2 : (a : ℚ) > 0 := by exact_mod_cast ha
    have eq3 : (b : ℚ) > 0 := by exact_mod_cast hb
    field_simp [ne_of_gt eq2, ne_of_gt eq3] at h
    nlinarith
  have eq3 : a * b = 4 * a + b := by
    have h_eq1 : (a : ℚ) * (b : ℚ) = 4 * (a : ℚ) + (b : ℚ) := eq1
    exact_mod_cast h_eq1
  have h6 : a ≤ 5 := by
    by_contra h'
    push_neg at h'
    have h7 : a ≥ 6 := by omega
    have h8 : a * b = 4 * a + b := eq3
    have h9 : b ≤ 5 := by
      nlinarith [sq_nonneg (a - 5 : ℕ), sq_nonneg (b - 4 : ℕ)]
    interval_cases b <;> omega
  interval_cases a <;> omega