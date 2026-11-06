import Mathlib

theorem algebra_96204 {p n : ℕ} (hp : p + n = 13) (hn : n + 1 = p) :
    p * 1 + n * 5 = 37 := by 
  have hp_eq : p = n + 1 := by 
    omega
  rw [hp_eq] at hp
  have hn_eq : n = 6 := by 
    omega
  have hp_eq2 : p = 7 := by 
    omega
  calc
    p * 1 + n * 5 = 7 * 1 + 6 * 5 := by rw [hp_eq2, hn_eq]
    _ = 7 + 30 := by norm_num
    _ = 37 := by norm_num