import Mathlib

theorem algebra_7976 {x y : ℤ} {n : ℕ} (hn : n > 2) (hx : x = 3 ^ n + 3 ^ (n + 1)) (hy : y = 3 ^ (n - 2) + 3 ^ (n - 1)) :
    x = 9 * y := by 
  rw [hx, hy]
  have h1 : n ≥ 3 := by omega
  have eq1 : (3 : ℤ) ^ n + (3 : ℤ) ^ (n + 1) = 4 * (3 : ℤ) ^ n := by 
    ring_nf
  have eq2 : (3 : ℤ) ^ (n + 1) = 3 * ((3 : ℤ) ^ n) := by 
    ring_nf
  have eq3 : (3 : ℤ) ^ (n - 2) + (3 : ℤ) ^ (n - 1) = 4 * (3 : ℤ) ^ (n - 2) := by
    have h4 : n - 1 = (n - 2) + 1 := by omega
    rw [h4]
    ring_nf
  have eq4 : (3 : ℤ) ^ n = 9 * ((3 : ℤ) ^ (n - 2)) := by 
    have h5 : n - 2 + 2 = n := by omega
    have eq5 : (3 : ℤ) ^ n = (3 : ℤ) ^ ((n - 2) + 2) := by 
      rw [show (n - 2) + 2 = n by omega]
    rw [eq5]
    ring_nf
  rw [eq1]
  rw [eq3]
  rw [eq4]
  all_goals 
    ring_nf