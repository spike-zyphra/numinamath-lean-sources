import Mathlib

theorem algebra_302640 {x a : ℝ} (ha : a ≠ 1) (h : x ≠ 1) (h1 : x + 1 / (x - 1) = a + 1 / (a - 1)) :
    x = a ∨ x = a / (a - 1) := by 
  have h2 : x - 1 ≠ 0 := by 
    intro h3
    apply h
    linarith
  have h3 : a - 1 ≠ 0 := by
    intro h4
    apply ha
    linarith
  have eq1 : (x + 1 / (x - 1)) * ((x - 1) * (a - 1)) = (a + 1 / (a - 1)) * ((x - 1) * (a - 1)) := by 
    rw [h1]
  have eq2 : (x + 1 / (x - 1)) * ((x - 1) * (a - 1)) = x * (x - 1) * (a - 1) + (a - 1) := by 
    field_simp [(show x - 1 ≠ 0 by exact h2)]
    <;> ring
  have eq3 : (a + 1 / (a - 1)) * ((x - 1) * (a - 1)) = a * (x - 1) * (a - 1) + (x - 1) := by 
    field_simp [(show a - 1 ≠ 0 by exact h3)]
    <;> ring
  rw [eq2, eq3] at eq1 
  have eq6 : (x - a) * (x - a / (a - 1)) = 0 := by
    field_simp [(show a - 1 ≠ 0 by exact h3)] at eq1 ⊢ 
    nlinarith [sq_nonneg (x - a), sq_nonneg (x - a / (a - 1)), sq_pos_of_ne_zero (show a - 1 ≠ 0 by exact h3), sq_nonneg (x - 1)]
  cases' (mul_eq_zero.mp eq6) with h4 h5
  · 
    left 
    linarith
  · 
    right 
    have eq7 : x = a / (a - 1) := by
      field_simp [(show a - 1 ≠ 0 by exact h3)] at h5 ⊢
      linarith
    exact eq7