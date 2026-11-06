import Mathlib

theorem number_theory_6341 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ (1 / 8 : ℚ) = 1 / a + 1 / b}.ncard = 7 := by
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ (1 / 8 : ℚ) = 1 / a + 1 / b} = {
      (9, 72), (10, 40), (12, 24), (16, 16), (24, 12), (40, 10), (72, 9)
    } := by
    ext ⟨a, b⟩
    simp
    constructor
    · -- Assume 'h' : (a, b) in the left side set, prove in the right side set
      rintro ⟨ha, hb, heq⟩ 
      have h2 : (a : ℚ) > 0 := by exact_mod_cast (show a > 0 by linarith)
      have h3 : (b : ℚ) > 0 := by exact_mod_cast (show b > 0 by linarith)
      have h4 : (a * b : ℚ) = 8 * b + 8 * a := by
        have h5 : (a : ℚ) ≠ 0 := by positivity
        have h6 : (b : ℚ) ≠ 0 := by positivity
        field_simp at heq ⊢
        nlinarith 
      have h7 : (a * b : ℕ) = 8 * b + 8 * a := by
        exact_mod_cast h4
      have h8 : a * b = 8 * b + 8 * a := by
        exact_mod_cast h4
      have h9 : a ≤ 72 := by
        by_contra h
        push_neg at h
        have h10 : b ≤ 8 := by
          nlinarith [show a * b = 8 * b + 8 * a by linarith [h7]]
        interval_cases b <;> try { 
          omega 
        }
      have h10 : b ≤ 72 := by 
        by_contra h
        push_neg at h
        have h11 : a ≤ 8 := by 
          nlinarith [show a * b = 8 * b + 8 * a by linarith [h7]]
        interval_cases a <;> try { 
          omega 
        }
      interval_cases a <;> omega
    · -- Assume (a, b) in the right side set, prove in the left side set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Verify (9, 72)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Verify (10, 40)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Verify (12, 24)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Verify (16, 16)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Verify (24, 12)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Verify (40, 10)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Verify (72, 9)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try native_decide