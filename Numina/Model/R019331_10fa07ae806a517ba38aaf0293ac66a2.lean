import Mathlib

theorem algebra_261906 (a : ℤ) (h : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    abs (abs (x - 2) - 1) = a ∧ abs (abs (y - 2) - 1) = a ∧
    abs (abs (z - 2) - 1) = a) :
    a = 1 := by
  rcases h with ⟨x, y, z, hx1, hy1, hz1, h1, h2, h3⟩
  by_contra h4
  push_neg at h4
  have eq1 : abs (abs (x - 2) - 1) = a := h1
  have eq2 : abs (abs (y - 2) - 1) = a := h2
  have eq3 : abs (abs (z - 2) - 1) = a := h3

  have hx_eq : abs (abs (x - 2) - 1) = abs (abs (y - 2) - 1) := by 
    rw [eq1, eq2]

  have hy_eq : abs (abs (y - 2) - 1) = abs (abs (z - 2) - 1) := by 
    rw [eq2, eq3]

  cases' abs_cases (abs (x - 2) - 1) with h11 h11 <;> 
  cases' abs_cases (abs (y - 2) - 1) with h12 h12 <;> 
  cases' abs_cases (abs (z - 2) - 1) with h13 h13 <;> 
  cases' abs_cases (x - 2) with h21 h21 <;> 
  cases' abs_cases (y - 2) with h22 h22 <;> 
  cases' abs_cases (z - 2) with h23 h23 <;> 
  omega