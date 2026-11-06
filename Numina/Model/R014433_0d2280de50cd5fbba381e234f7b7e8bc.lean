import Mathlib

theorem algebra_113905 :
    {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ (4 / m : ℚ) + (2 / n : ℚ) = 1}.ncard = 4 := by
  have h1 : {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ (4 / m : ℚ) + (2 / n : ℚ) = 1} = {(5, 10), (6, 6), (8, 4), (12, 3)} := by
    ext ⟨m, n⟩
    simp
    constructor
    · -- Assume (m, n) is in the set
      rintro ⟨hm, hn, heq⟩
      have h2 : (m : ℚ) > (0 : ℚ) := by exact_mod_cast hm
      have h3 : (n : ℚ) > (0 : ℚ) := by exact_mod_cast hn
      have h4 : (m : ℚ) * (n : ℚ) = 4 * (n : ℚ) + 2 * (m : ℚ) := by
        field_simp at heq ⊢
        linarith
      have h5 : (m : ℕ) * (n : ℕ) = 4 * (n : ℕ) + 2 * (m : ℕ) := by
        exact_mod_cast h4
      have h6 : m * n = 4 * n + 2 * m := by 
        linarith [h5]
      have h7 : m ≤ 12 := by
        by_contra h
        push_neg at h
        have h8 : n ≤ 3 := by
          nlinarith [show m * n = 4 * n + 2 * m from h6]
        interval_cases n <;> omega
      have h8 : n ≤ 12 := by
        by_contra h
        push_neg at h
        have h9 : m ≤ 4 := by
          nlinarith [show m * n = 4 * n + 2 * m from h6]
        interval_cases m <;> omega
      interval_cases m <;> omega
    · -- Show that each of the four pairs is in the set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
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
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }