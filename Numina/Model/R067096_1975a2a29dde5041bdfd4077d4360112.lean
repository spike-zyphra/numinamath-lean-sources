import Mathlib

theorem algebra_93725 :
    {(M, N) : ℕ × ℕ | M > 0 ∧ N > 0 ∧ (M / 6 : ℚ) = 6 / N}.encard = 9 := by
  have h_eq : {(M, N) : ℕ × ℕ | M > 0 ∧ N > 0 ∧ (M / 6 : ℚ) = 6 / N} = 
      {(1, 36), (2, 18), (3, 12), (4, 9), (6, 6), (9, 4), (12, 3), (18, 2), (36, 1)} := by
    ext ⟨M, N⟩
    simp
    constructor
    · -- Show that (M, N) satisfies the equation implies it's in the explicit set
      rintro ⟨hM, hN, h_eq⟩
      have h_eq2 : (M : ℚ) * (N : ℚ) = 36 := by
        have h_eq1 : (M : ℚ)/6 = 6/(N : ℚ) := by
          exact_mod_cast h_eq
        have h1 : (N : ℚ) ≠ 0 := by
          exact_mod_cast show N ≠ 0 by omega
        field_simp at h_eq1 ⊢
        linarith
      have h_eq_nat : M * N = 36 := by
        have h_eq2_nat : (M : ℚ) * (N : ℚ) = 36 := by assumption
        have : (M * N : ℚ) = 36 := by
          have h1 : (M : ℚ) * (N : ℚ) = 36 := by assumption
          norm_num at h1 ⊢
          linarith
        have h2 : M * N = 36 := by
          exact_mod_cast this
        exact h2
      have h1 : M ≤ 36 := by
        nlinarith [h_eq_nat, hN]
      have h2 : N ≤ 36 := by
        nlinarith [h_eq_nat, hM]
      interval_cases M <;> omega
    · -- Show that the explicit set satisfies the equation
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h_eq]
  rw [Set.encard]
  simp [Set.ncard]
  <;> aesop