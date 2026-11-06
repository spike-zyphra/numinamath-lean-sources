import Mathlib

theorem algebra_78677 :
    {(m, n) : ℤ × ℤ | m * n + n + 14 = (m - 1)^2}.encard = 8 := by
  have h1 : {(m, n) : ℤ × ℤ | m * n + n + 14 = (m - 1)^2} = { (0, -13), (-2, 5), (1, -7), (-3, -1), (4, -1), (-6, -7), (9, 5), (-11, -13) } := by
    ext ⟨m, n⟩
    simp 
    constructor 
    · -- First direction: If (m, n) is in the set, it's one of these pairs
      rintro H 
      have h2 : m * n + n + 14 = (m - 1)^2 := H 
      have h3 : (m + 1) * n = m^2 - 2 * m - 13 := by 
        nlinarith 
      have h4 : m + 1 ∣ m^2 - 2 * m - 13 := by 
        use n 
        all_goals linarith 
      have h5 : m + 1 ∣ 10 := by 
        have h6 : m + 1 ∣ m^2 - 2 * m - 13 := h4 
        have h7 : m + 1 ∣ (m + 1) * (m - 3) := by 
          use m - 3 
          all_goals ring 
        have h8 : m + 1 ∣ ( (m + 1) * (m - 3) - (m^2 - 2 * m - 13) ) := by 
          apply Dvd.dvd.sub 
          · -- Show that m + 1 divides (m + 1) * (m - 3)
            exact h7 
          · -- Show that m + 1 divides m^2 - 2 * m - 13 
            exact h4 
        have h9 : ( (m + 1) * (m - 3) - (m^2 - 2 * m - 13) ) = 10 := by 
          ring_nf 
        rw [h9] at h8 
        exact h8 
      have h6 : m + 1 ∣ 10 := h5 
      have h7 : m + 1 ≤ 10 := by 
        apply Int.le_of_dvd (by norm_num) h6 
      have h8 : m + 1 ≥ -10 := by 
        have h8 : -(m + 1) ∣ 10 := by 
          exact Int.neg_dvd.2 h6 
        have h9 : -(m + 1) ≤ 10 := by 
          apply Int.le_of_dvd (by norm_num) h8 
        linarith 
      have h9 : m ≥ -11 := by 
        linarith 
      have h10 : m ≤ 9 := by 
        linarith 
      interval_cases m <;> omega 
    · -- Second direction: These pairs are in the set 
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ )
      · -- Check (0, -13)
        norm_num 
      · -- Check (-2, 5)
        norm_num 
      · -- Check (1, -7)
        norm_num 
      · -- Check (-3, -1)
        norm_num 
      · -- Check (4, -1)
        norm_num 
      · -- Check (-6, -7)
        norm_num 
      · -- Check (9, 5)
        norm_num 
      · -- Check (-11, -13)
        norm_num 
  rw [h1] 
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }