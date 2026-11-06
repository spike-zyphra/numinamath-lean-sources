import Mathlib

theorem number_theory_145007 : (Nat.floor ((10^20000 : ℝ) / (10^100 + 3)) % 10) = 3 := by 
  have h1 : Nat.floor ((10^20000 : ℝ) / (10^100 + 3)) = (10^20000 - 29) / (10^100 + 3) := by
    norm_num [Nat.floor_eq_iff]
    <;> try { native_decide }
  rw [h1]
  norm_num
  <;> try { native_decide }