import Mathlib

theorem number_theory_128839 :
    Set.ncard {n : ℤ | n ∈ Finset.Icc (-50) 250 ∧ 13 ∣ n^3 - 2 * n^2 - 13 * n - 10} = 69 ∧
    IsGreatest {x | ∃ n : ℤ, n ∈ Finset.Icc (-50) 250 ∧ x = n ∧ 13 ∣ n^3 - 2 * n^2 - 13 * n - 10} 246 ∧
    IsLeast {x | ∃ n : ℤ, n ∈ Finset.Icc (-50) 250 ∧ x = n ∧ 13 ∣ n^3 - 2 * n^2 - 13 * n - 10} (-47) := by 
  have h1 : {n : ℤ | n ∈ Finset.Icc (-50) 250 ∧ 13 ∣ n^3 - 2 * n^2 - 13 * n - 10} = Finset.filter (fun n => 13 ∣ n^3 - 2 * n^2 - 13 * n - 10) (Finset.Icc (-50 : ℤ) 250) := by
    ext n
    simp
  rw [h1] at *
  constructor
  · -- Show the cardinality is 69
    rw [Set.ncard_coe_Finset]
    native_decide
  constructor
  · -- Show 246 is greatest
    constructor
    · -- Show 246 is in the set
      use 246
      native_decide
    · -- Show 246 is the greatest
      intro x hx
      rcases hx with ⟨n, hn1, h2, hn2⟩
      rw [Finset.mem_Icc] at hn1
      rcases hn1 with ⟨hn1l, hn1r⟩
      by_contra h
      push_neg at h
      have h4 : n > 246 := by linarith 
      have h5 : n ≤ 250 := by linarith 
      interval_cases n <;> omega 
  · -- Show -47 is the least 
    constructor 
    · -- Show -47 is in the set
      use -47 
      native_decide 
    · -- Show -47 is the least 
      intro x hx 
      rcases hx with ⟨n, hn1, h2, hn2⟩ 
      rw [Finset.mem_Icc] at hn1 
      rcases hn1 with ⟨hn1l, hn1r⟩ 
      by_contra h 
      push_neg at h 
      have h6 : n < -47 := by linarith 
      have h7 : n ≥ -50 := by linarith 
      interval_cases n <;> omega