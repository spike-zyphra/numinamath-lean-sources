import Mathlib

theorem number_theory_235020 :
    Set.ncard {n : ℕ | n ∈ [123, 234, 345, 456, 567] ∧ 3 ∣ n} = 5 := by 
  have h : {n : ℕ | n ∈ [123, 234, 345, 456, 567] ∧ 3 ∣ n} = {123, 234, 345, 456, 567} := by 
    ext n 
    simp 
    omega 
  rw [h] 
  norm_num