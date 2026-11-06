import Mathlib

theorem algebra_145721 (n : ℕ) :
    7^(2*n+3)*7^(3*n+2)/(49*7^(5*n)) = 343 := by
  have eq1 : 7 ^ (2 * n + 3) * 7 ^ (3 * n + 2) = 7 ^ (5 * n + 5) := by
    ring_nf
  have eq2 : 49 * 7 ^ (5 * n) = 7 ^ (5 * n + 2) := by
    have eq3 : 49 = 7 ^ 2 := by norm_num
    rw [eq3]
    ring_nf
  rw [eq1, eq2]
  have eq3 : 7 ^ (5 * n + 5) / (7 ^ (5 * n + 2)) = 7 ^ 3 := by
    have h1 : 7 ^ (5 * n + 5) = 7 ^ (5 * n + 2) * 7 ^ 3 := by
      ring_nf
    rw [h1]
    field_simp
    <;> omega
  rw [eq3]
  all_goals norm_num