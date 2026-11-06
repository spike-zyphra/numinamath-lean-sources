import Mathlib

set_option linter.unusedVariables false
/- If x=am+bn satisfies the quadratic equation (x+m)^2−(x+n)^2=(m−n)^2, where m and n are unequal and non-zero constants, then a=0, and b has a unique non-zero value -/
theorem algebra_265308 {x a b m n : ℝ} (hx : x = a * m + b * n) (h : (x + m) ^ 2 - (x + n) ^ 2 = (m - n) ^ 2) (hmn : m ≠ n) (hm : m ≠ 0) (hn : n ≠ 0) : (a = 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = 0) := by
  -- Apply the difference of square formula
  have aux1 : (x + m + (x + n)) * (x + m - (x + n)) = ( m - n ) ^ 2 := by
    rw[← h]
    ring
  have aux2 : m - n ≠ 0 := by
    contrapose! hmn
    linarith
  field_simp at aux1
  have aux3 : (m - n) ^ 2 = (m - n) * (m - n) := by
    linarith
  rw [aux3] at aux1
  field_simp at aux1
  have aux4 : x + m + (x + n) = m - n := by
    tauto
  have hx : a * m + b * n = -n := by
    linarith
  -- When a=0, show that b is unique and not equal to 0
  by_cases ha : a = 0
  have hb : b = -1 := by
    rw [ha] at hx
    have aux5 : b * n = (-1 : ℝ) * n := by
      simpa [neg_one_mul] using hx
    exact mul_right_cancel₀ hn aux5
  left
  constructor
  linarith
  linarith
  -- When a≠0, show that the case is valid
  right
  tauto
