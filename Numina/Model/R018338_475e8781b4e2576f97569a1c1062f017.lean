import Mathlib

theorem algebra_11564 (M : ℤ) (hM : M = sSup {z | ∃(a b : ℤ), 0 < a ∧ 0 < b ∧ a * b + a - b - 5 = 0 ∧ z = a ^ 2 + b ^ 2}) :
    Set.encard {(x, y) : ℤ × ℤ | 3 * x ^ 2 + 2 * y ^ 2 ≤ M} = 17 := by

  have h1 : M = 13 := by
    rw [hM]
    have h2 : {z | ∃ (a b : ℤ), 0 < a ∧ 0 < b ∧ a * b + a - b - 5 = 0 ∧ z = a ^ 2 + b ^ 2} = {10, 13} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · -- Assume z in the set
        rintro ⟨a, b, ha, hb, heq, hz⟩
        have h_eq : a * b + a - b - 5 = 0 := heq
        have h_eq2 : (a - 1) * (b + 1) = 4 := by
          nlinarith
        have h3 : (a - 1) ∣ 4 := by
          use (b + 1)
          all_goals linarith
        have h4 : (a - 1) ≥ 1 := by
          nlinarith
        have h5 : (a - 1) ≤ 4 := by
          have h6 : (a - 1) ∣ 4 := h3
          have h7 : (a - 1) ≤ 4 := by
            exact Int.le_of_dvd (by norm_num) h6
          linarith
        have h8 : (a - 1) = 1 ∨ (a - 1) = 2 ∨ (a - 1) = 4 := by
          interval_cases h : (a - 1) <;> tauto
        rcases h8 with (h11 | h12 | h13)
        · -- Case h11: a - 1 = 1
          have h41 : a = 2 := by 
            linarith
          have h31 : b = 3 := by
            nlinarith
          rw [hz, h41, h31]
          norm_num
        · -- Case h12: a - 1 = 2
          have h42 : a = 3 := by 
            linarith
          have h32 : b = 1 := by
            nlinarith
          rw [hz, h42, h32]
          norm_num
        · -- Case h13: a - 1 = 4
          have h43 : a = 5 := by 
            linarith
          have h33 : b = 0 := by
            nlinarith
          nlinarith
      · -- Assume z is either 10 or 13
        rintro (rfl | rfl)
        · -- Show z=10 is in the set
          refine ⟨3, 1, by norm_num, by norm_num, ?_, ?_⟩
          all_goals norm_num
        · -- Show z=13 is in the set
          refine ⟨2, 3, by norm_num, by norm_num, ?_, ?_⟩
          all_goals norm_num
    rw [h2]
    norm_num [sSup_pair]
  rw [h1]
  have h4 : {(x, y) : ℤ × ℤ | 3 * x ^ 2 + 2 * y ^ 2 ≤ 13} = Finset.filter (fun p : ℤ × ℤ => 3 * p.1 ^ 2 + 2 * p.2 ^ 2 ≤ 13) (Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.Icc (-2 : ℤ) 2) := by
    ext ⟨x, y⟩
    simp
    intro h
    have h1 : x ≥ -2 := by nlinarith
    have h2 : x ≤ 2 := by nlinarith
    have h3 : y ≥ -2 := by nlinarith
    have h4 : y ≤ 2 := by nlinarith
    omega
  rw [h4]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide