import Mathlib

theorem algebra_299266 :
    {(m, n) : ℤ × ℤ | m ≠ 0 ∧ n ≠ 0 ∧ (2011 / m : ℚ) + (1 / n : ℚ) = 1}.ncard = 3 := by
  have h1 : {(m, n) : ℤ × ℤ | m ≠ 0 ∧ n ≠ 0 ∧ (2011 / m : ℚ) + (1 / n : ℚ) = 1} = { 
    (2012, 2012), (4022, 2), (2010, -2010)
    } := by 
    ext ⟨m, n⟩
    simp
    constructor
    · -- First, prove that (m, n) satisfies the equation implies (m, n) ∈ {(2012, 2012), (4022, 2), (2010, -2010)}
      rintro ⟨hm, hn, heq⟩
      have h_eq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
      have h_eq2 : (n : ℚ) ≠ 0 := by exact_mod_cast hn
      have h3 : (2011 : ℚ) * n + (m : ℚ) = (m : ℚ) * (n : ℚ) := by
        have h_eq1 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
        have h_eq2 : (n : ℚ) ≠ 0 := by exact_mod_cast hn
        field_simp at heq ⊢
        linarith
      have h4 : 2011 * n + m = m * n := by
        have h_eq1 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
        have h_eq2 : (n : ℚ) ≠ 0 := by exact_mod_cast hn
        have h5 : (2011 : ℚ) * n + (m : ℚ) = (m : ℚ) * (n : ℚ) := by linarith
        norm_num at h5 ⊢
        have h6 : (2011 * n + m : ℚ) = (m * n : ℚ) := by linarith
        have h7 : (2011 * n + m : ℚ) = (m * n : ℚ) := by linarith
        have h8 : (2011 * n + m : ℤ) = (m * n : ℤ) := by 
          exact_mod_cast h7
        linarith
      have h9 : (m - 2011) * (n - 1) = 2011 := by 
        nlinarith
      have h10 : m - 2011 ∣ 2011 := by 
        use n - 1
        linarith
      have h11 : m - 2011 = 1 ∨ m - 2011 = 2011 ∨ m - 2011 = -1 ∨ m - 2011 = -2011 := by
        have h12 : m - 2011 ∣ 2011 := h10
        have h13 : m - 2011 ≤ 2011 := by 
          apply Int.le_of_dvd (by norm_num) h12
        have h14 : m - 2011 ≥ -2011 := by 
          have h15 : -(m - 2011) ∣ 2011 := by 
            exact Int.neg_dvd.2 h12
          have h16 : -(m - 2011) ≤ 2011 := by 
            apply Int.le_of_dvd (by norm_num) h15
          linarith
        interval_cases h : m - 2011 <;> omega
      rcases h11 with h | h | h | h
      · -- m - 2011 = 1
        have hm2 : m = 2012 := by linarith
        have hn2 : n = 2012 := by
          nlinarith [h9, h]
        simp [hm2, hn2]
      · -- m - 2011 = 2011
        have hm2 : m = 4022 := by linarith
        have hn2 : n = 2 := by
          nlinarith [h9, h]
        simp [hm2, hn2]
      · -- m - 2011 = -1
        have hm2 : m = 2010 := by linarith
        have hn2 : n = -2010 := by
          nlinarith [h9, h]
        simp [hm2, hn2]
      · -- m - 2011 = -2011
        have hm2 : m = 0 := by linarith
        contradiction
    · -- Now prove the reverse direction
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (2012, 2012)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (4022, 2)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (2010, -2010)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }