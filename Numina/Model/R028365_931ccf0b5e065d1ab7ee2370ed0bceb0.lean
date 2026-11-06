import Mathlib

theorem number_theory_11054  :
  IsGreatest {n | ∃ A B C, A ≠ B ∧ B ≠ C ∧ C ≠ A ∧ A ∈ Finset.Icc 1 9 ∧ B ∈ Finset.Icc 0 9 
    ∧ C ∈ Finset.Icc 0 9 ∧ 11 ∣ Nat.ofDigits 10 [A, B, C, B, A] ∧
    n = Nat.ofDigits 10 [A, B, C, B, A]} 96569 := by
  constructor
  · -- Show 96569 is in the set
    use 9, 6, 5
    all_goals native_decide
  · -- Show there is no greater element in the set
    intro n hn 
    rcases hn with ⟨A, B, C, h1, h2, h3, h4, h5, h6, h7, hn⟩
    rw [hn]
    norm_num [Nat.ofDigits] at h7 ⊢
    have h8 : A ≤ 9 := by
      simp [Finset.mem_Icc] at h4 
      omega
    have h9 : A ≥ 1 := by
      simp [Finset.mem_Icc] at h4
      omega
    have h10 : B ≤ 9 := by 
      simp [Finset.mem_Icc] at h5 
      omega 
    have h11 : C ≤ 9 := by 
      simp [Finset.mem_Icc] at h6 
      omega 
    interval_cases A <;> interval_cases B <;> interval_cases C <;> omega