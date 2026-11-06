import Mathlib

theorem number_theory_108427 : (Nat.floor (10^20000 / (10^100 + 3)) % 10) = 3 := by
  have h1 : Nat.floor (10^20000 / (10^100 + 3)) = (10^20000 / (10^100 + 3)) := by 
    simp
  rw [h1]
  norm_num