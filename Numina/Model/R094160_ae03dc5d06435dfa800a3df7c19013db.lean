import Mathlib

theorem number_theory_196097 (x : ℕ) (hx : x ∈ Finset.Icc 100 999) (h7 : 7 ∣ x - 7) (h8 : 8 ∣ x - 8) (h9 : 9 ∣ x - 9) :
    x = 504 := by
  have h5 : x ≥ 100 := by
    simp [Finset.mem_Icc] at hx 
    omega
  have h5' : x ≤ 999 := by
    simp [Finset.mem_Icc] at hx 
    omega
  
  interval_cases x <;> norm_num at h7 h8 h9 
    <;> omega