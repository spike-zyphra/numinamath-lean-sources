import Mathlib

theorem number_theory_464 :
    (Finset.Icc 1 50).card = 50 ∧
    {n : ℕ | n ∈ Finset.Icc 1 50 ∧ Nat.Prime n ∧ 7 ∣ n}.ncard = 1 := by
  constructor
  · -- Show that the set from 1 to 50 has 50 elements
    native_decide

  · -- Show that the set of numbers from 1 to 50 that are both prime and divisible by 7 has cardinality 1
    have h1 : {n : ℕ | n ∈ Finset.Icc 1 50 ∧ Nat.Prime n ∧ 7 ∣ n} = {7} := by
      ext n
      simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · -- Assume n ∈ {n : ℕ | n ∈ Finset.Icc 1 50 ∧ Nat.Prime n ∧ 7 ∣ n}
        intro h
        rcases h with ⟨⟨hn1, hn2⟩, h3, h4⟩
        interval_cases n <;> tauto

      · -- Assume n = 7
        intro h
        rw [h]
        constructor
        · -- Show 7 ∈ [1, 50]
          exact ⟨by norm_num, by norm_num⟩
        constructor
        · -- Show 7 is prime
          norm_num
        · -- Show 7 is divisible by 7
          norm_num

    rw [h1]
    simp