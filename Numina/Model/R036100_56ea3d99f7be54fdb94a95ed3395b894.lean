import Mathlib

theorem number_theory_237970 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 2010 2099 ∧ ∃ k, (n / 100) * (n % 100) = k ^ 2} = 3 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 2010 2099 ∧ ∃ k, (n / 100) * (n % 100) = k ^ 2} = {2020, 2045, 2080} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is in the set
      rintro ⟨⟨hn1, hn2⟩, ⟨k, h⟩⟩
      have h2 : n ≥ 2010 := by linarith
      have h3 : n ≤ 2099 := by linarith
      have h4 : n / 100 = 20 := by
        omega
      have h5 : n % 100 ≤ 99 := by
        omega
      have h6 : n % 100 ≥ 10 := by
        omega
      rw [h4] at h
      have h7 : k ≤ 44 := by
        nlinarith [h, h5]
      have h8 : k ≥ 15 := by
        nlinarith [h, h6]
      interval_cases k <;> omega
    · -- Assume n in {2020, 2045, 2080}, so prove it has the property
      rintro (rfl | rfl | rfl)
      · -- n = 2020
        constructor
        · -- 2020 is in the range [2010, 2099]
          norm_num
        · -- There exists k such that (2020 / 100) * (2020 % 100) = k^2
          use 20
          all_goals norm_num
      · -- n = 2045
        constructor
        · -- 2045 is in the range [2010, 2099]
          norm_num
        · -- There exists k such that (2045 / 100) * (2045  % 100) = k^2
          use 30
          all_goals norm_num
      · -- n = 2080
        constructor
        · -- 2080 is in the range [2010, 2099]
          norm_num
        · -- There exists k such that (2080 / 100) * (2080  % 100) = k^2
          use 40
          all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> native_decide