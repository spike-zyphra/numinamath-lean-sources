import Mathlib

theorem algebra_16361 {p n : ℕ} (hp : p.Prime) (h : p = n^2 + 4) (h' : p = (n + 1)^2 - 7) :
    p = 29 := by
  have eq1 : n^2 + 4 = (n + 1)^2 - 7 := by 
    rw [←h, ←h']
  have eq2 : (n + 1: ℕ)^2 = n^2 + 2 * n + 1 := by 
    ring
  have eq3 : (n + 1: ℕ)^2 - 7 = n^2 + 2 * n + 1 - 7 := by 
    rw [eq2]
  rw [eq3] at eq1
  have eq4 : n = 5 := by
    have eq6 : n^2 + 4 = n^2 + 2 * n + 1 - 7 := eq1
    omega
  have eq5 : p = 29 := by 
    rw [h]
    have n5 : n = 5 := eq4
    rw [n5]
    all_goals
      nlinarith
  exact eq5