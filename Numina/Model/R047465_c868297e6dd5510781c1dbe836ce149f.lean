import Mathlib

theorem algebra_136965 :
    {(m, n) : ℕ × ℕ | 0 < m ∧ 0 < n ∧ (3 / m : ℚ) + (2 / n : ℚ) = 1}.ncard = 4 := by 
  have h1 : {(m, n) : ℕ × ℕ | 0 < m ∧ 0 < n ∧ (3 / m : ℚ) + (2 / n : ℚ) = 1} = {(4, 8), (5, 5), (6, 4), (9, 3)} := by
    ext ⟨m, n⟩
    simp
    constructor
    · -- Assume (m, n) is in the set
      rintro ⟨hm, hn, heq⟩
      have eq1 : (m : ℚ) > 0 := by exact_mod_cast hm
      have eq2 : (n : ℚ) > 0 := by exact_mod_cast hn
      have eq3 : 3 * (n : ℚ) + 2 * (m : ℚ) = (m : ℚ) * (n : ℚ) := by
        have h : (m : ℚ) ≠ 0 := by positivity
        have h2 : (n : ℚ) ≠ 0 := by positivity
        field_simp at heq ⊢
        linarith
      have eq4 : 3 * (n : ℕ) + 2 * (m : ℕ) = (m : ℕ) * (n : ℕ) := by
        exact_mod_cast eq3
      have h2 : m ≤ 9 := by
        by_contra h
        push_neg at h
        have h3 : n ≤ 6 := by
          nlinarith [eq4]
        interval_cases n <;> try { 
          omega
        }
      have h3 : n ≤ 9 := by
        by_contra h
        push_neg at h
        have h4 : m ≤ 6 := by
          nlinarith [eq4]
        interval_cases m <;> try { 
          omega
        }
      interval_cases m <;> interval_cases n <;> norm_num at eq4 ⊢
    · -- Show that these four pairs satisfy the condition
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (4, 8)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (5, 5)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (6, 4)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (9, 3)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }