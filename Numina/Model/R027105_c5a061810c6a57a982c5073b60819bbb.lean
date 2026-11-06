import Mathlib

theorem number_theory_283931 (A B : ℕ) (hA : A ∈ Finset.Icc 1000 9999) (hB : B ∈ Finset.Icc 1000 9999)
    (hAB : A * B = 16^5 + 2^10) : A + B = 2049 := by 
  rw [Finset.mem_Icc] at hA hB 
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  norm_num at hAB 
  have h4 : A ≤ 1049 := by 
    nlinarith [hAB, hB1, hB2]
  have h5 : A ≥ 1000 := by linarith 
  have h3 : A = 1024 ∨ A = 1025 := by 
    interval_cases A <;> omega 
  rcases h3 with (hA_eq | hA_eq)
  · -- Case A = 1024 
    have hB_eq : B = 1025 := by 
      rw [hA_eq] at hAB 
      nlinarith 
    omega 
  · -- Case A = 1025 
    have hB_eq : B = 1024 := by 
      rw [hA_eq] at hAB 
      nlinarith 
    omega