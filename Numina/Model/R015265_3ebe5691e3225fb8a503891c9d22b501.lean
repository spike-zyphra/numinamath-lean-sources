import Mathlib

theorem algebra_177847 {x : ℝ} (hx : x ≠ -2 ∧ x ≠ -3 ∧ x ≠ -1) :
    1 + 3 / (x + 3) * (1 + 2 / (x + 2) * (1 + 1 / (x + 1))) = x ↔ x = 2 := by
  constructor
  · -- Assume the equation holds, prove x = 2
    intro h
    have h1 : x ≠ -2 := hx.1
    have h2 : x ≠ -3 := hx.2.1
    have h3 : x ≠ -1 := hx.2.2
    have hx1 : x + 1 ≠ 0 := by
      intro h'
      apply h3
      linarith
    have hx2 : x + 2 ≠ 0 := by
      intro h'
      apply h1
      linarith
    have hx3 : x + 3 ≠ 0 := by
      intro h'
      apply h2
      linarith
    have eq1 : 1 + 3 / (x + 3) * (1 + 2 / (x + 2) * (1 + 1 / (x + 1))) = (x + 4) / (x + 1) := by
      field_simp [hx1, hx2, hx3]
      ring
    rw [eq1] at h
    have eq2 : x + 1 ≠ 0 := by
      intro h'
      apply h3
      linarith
    have eq3 : x + 4 = x * (x + 1) := by
      field_simp [eq2] at h
      linarith
    have eq4 : x ^ 2 - 4 = 0 := by
      nlinarith [eq3]
    have eq5 : (x - 2) * (x + 2) = 0 := by
      nlinarith [eq4]
    cases' (mul_eq_zero.mp eq5) with h6 h7
    · -- x - 2 = 0
      linarith
    · -- x + 2 = 0
      exfalso
      apply h1
      linarith
  · -- Assume x = 2, prove the equation
    intro h
    rw [h]
    norm_num