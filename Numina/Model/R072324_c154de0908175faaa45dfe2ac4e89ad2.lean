import Mathlib

theorem number_theory_97917 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ Even n ∧ (Nat.digits 10 n).sum = 26} = 1 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ Even n ∧ (Nat.digits 10 n).sum = 26} = {998} := by
    ext n
    simp [Finset.mem_Icc, Nat.even_iff]
    constructor
    · -- Assume n is in the set
      rintro ⟨⟨hn1, hn2⟩, hneven, hsum⟩
      interval_cases n <;> norm_num at hneven hsum <;> omega
    · -- Assume n = 998, we need to show it's in the set
      intro h
      rw [h]
      all_goals norm_num
      <;> native_decide
  rw [h1]
  simp