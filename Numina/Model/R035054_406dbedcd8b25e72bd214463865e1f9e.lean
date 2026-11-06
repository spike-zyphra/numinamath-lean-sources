import Mathlib

theorem Algebra_1186 (T C N : ℤ) (hN : N ≠ 0) (h1 : T = C) (h2 : T - N = 2*(C - 3*N)) : T/N = 5 := by 
  -- Substitute T = C into the second equation
  have eq1 : C = 5 * N := by
    have eq2 : T - N = 2 * (C - 3 * N) := h2
    rw [show T = C by linarith [h1]] at eq2
    linarith
  
  have eq2 : T = 5 * N := by
    have eq3 : T = C := by linarith [h1]
    rw [eq3]
    linarith [eq1]

  have eq3 : T = 5 * N := eq2
  
  have eq4 : T / N = 5 := by 
    rw [eq3]
    field_simp [hN]
    
  exact eq4