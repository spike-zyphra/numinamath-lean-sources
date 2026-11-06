import Mathlib

theorem algebra_209567 {x : ℝ} (hx : x ≠ 0 ∧ x ≠ -1 / 3) :
    ((x + 1) ^ 4 - 4 * (x + x ^ 2) ^ 2 + 4 * x ^ 2 - (1 + x) ^ 2) / (3 * x ^ 2 + x) = (x + 2) * (1 - x) := by

  have hx1 : x ≠ 0 := hx.1
  have hx2 : x ≠ -1/3 := hx.2

  have h1 : 3 * x ^ 2 + x ≠ 0 := by
    by_contra h
    have : x * (3 * x + 1) = 0 := by linarith 
    cases' (mul_eq_zero.mp this) with h2 h3
    · -- x = 0 
      exfalso
      exact hx1 (by linarith)
    · -- 3x + 1 = 0, so x = -1/3
      have h4 : x = -1/3 := by linarith
      exfalso
      exact hx2 (by linarith)
  
  field_simp [h1]
  ring