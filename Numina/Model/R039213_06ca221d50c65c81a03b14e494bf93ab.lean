import Mathlib

theorem algebra_10697 :
    {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ (1 / m : ℚ) + (1 / n : ℚ) = 1 / 4}.ncard = 5 := by
  have h1 : {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ (1 / m : ℚ) + (1 / n : ℚ) = 1 / 4} = 
      {(5, 20), (6, 12), (8, 8), (12, 6), (20, 5)} := by
    ext ⟨m, n⟩
    simp
    constructor
    · -- Assume (m, n) satisfy the equation
      rintro ⟨hm, hn, heq⟩
      have h_eq : (m : ℚ) > 0 := by exact_mod_cast hm
      have h_eq' : (n : ℚ) > 0 := by exact_mod_cast hn
      have h_eq1 : (m : ℚ) * (n : ℚ) = 4 * (m : ℚ) + 4 * (n : ℚ) := by
        field_simp at heq
        nlinarith
      have h_eq2 : (m : ℤ) * (n : ℤ) = 4 * (m : ℤ) + 4 * (n : ℤ) := by 
        exact_mod_cast h_eq1
      have h_eq3 : m * n = 4 * m + 4 * n := by
        norm_num at h_eq2 ⊢
        omega
      have h2 : m ≤ 20 := by 
        by_contra h
        push_neg at h
        have h3 : n ≤ 4 := by
          by_contra h4
          push_neg at h4
          nlinarith [show m * n = 4 * m + 4 * n from h_eq3, h, h4]
        interval_cases n <;> try { 
          omega
        }
      have h3 : n ≤ 20 := by 
        by_contra h
        push_neg at h
        have  h4 : m ≤ 4 := by 
          by_contra h4 
          push_neg at h4
          nlinarith [show m * n = 4 * m + 4 * n from h_eq3, h, h4]
        interval_cases m <;> try { 
          omega 
        }
      interval_cases m <;> try { 
        omega 
      }
    · -- Show that these are indeed solutions 
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Show that (5, 20) is a solution 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Check that 1/5 + 1/20 = 1/4
          norm_num 
      · -- Show that (6, 12) is a solution 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Check that 1/6 + 1/12 = 1/4
          norm_num
      · -- Show that (8, 8) is a solution 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Check that 1/8 + 1/8 = 1/4 
          norm_num 
      · -- Show that (12, 6) is a solution 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Check that 1/12 + 1/6 = 1/4 
          norm_num 
      · -- Show that (20, 5) is a solution 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Check that 1/20 + 1/5 = 1/4 
          norm_num 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { 
    native_decide 
  }