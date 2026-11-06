import Mathlib

theorem number_theory_11399 :
    Set.ncard {n : ℕ | ∃ m, n = 3 * m + 2 ∧ ∃ k, n = 5 * k + 3 ∧ n ∈ Finset.Icc 1 2018} = 135 := by 
  have h1 : {n : ℕ | ∃ m, n = 3 * m + 2 ∧ ∃ k, n = 5 * k + 3 ∧ n ∈ Finset.Icc 1 2018} = Finset.filter (fun n => n % 15 = 8) (Finset.Icc 1 2018) := by
    ext n
    simp [Finset.mem_Icc]
    constructor
    · -- Assume n satisfies the left side conditions, prove it's in the right side
      rintro ⟨hm, hk, h1⟩
      rcases hm with ⟨m, hm⟩
      rcases hk with ⟨k, hk⟩
      have h2 : n % 15 = 8 := by 
        omega
      have h3 : n ≥ 1 := by 
        omega
      have h4 : n ≤ 2018 := by 
        omega
      have h5 : n ∈ Finset.Icc 1 2018 := by 
        simp at *
        all_goals omega
      tauto
    · -- Assume n is in the right side, prove it's in the left side
      rintro ⟨hn, hf⟩
      rcases hn with ⟨hn1, hn2⟩
      have h2 : ∃ m, n = 3 * m + 2 := by
        refine' ⟨5 * (n / 15) + 2, by omega⟩
      have h3 : ∃ k, n = 5 * k + 3 := by
        refine' ⟨3 * (n / 15) + 1, by omega⟩
      exact ⟨h2, h3, by simpa using ⟨hn1, hn2⟩⟩
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide