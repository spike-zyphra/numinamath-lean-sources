import Mathlib

theorem number_theory_22972 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 100 ∧ 3 ∣ n ∧ 4 ∣ n ∧ 5 ∣ n} = 1 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 100 ∧ 3 ∣ n ∧ 4 ∣ n ∧ 5 ∣ n} = {60} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- First direction: if n is in the left side, then it is in the right side.
      intro h
      rcases h with ⟨⟨hn1, hn2⟩, h3, h4, h5⟩
      have h7 : n = 60 := by
        have h60 : 60 ∣ n := by
          have h3' : n % 3 = 0 := by omega
          have h4' : n % 4 = 0 := by omega
          have h5' : n % 5 = 0 := by omega
          omega
        omega
      exact h7
    · -- Second direction: if n is in the right side, then it is in the left side.
      intro h
      rw [h]
      constructor
      · -- Show `1 ≤ 60 ∧ 60 ≤ 100`
        norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
  rw [h1]
  simp