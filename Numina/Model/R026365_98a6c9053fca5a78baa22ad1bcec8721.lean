import Mathlib

theorem algebra_18731 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ (1 / a : ℚ) + (1 / b : ℚ) = 2 / 17}.ncard = 3 := by
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ (1 / a : ℚ) + (1 / b : ℚ) = 2 / 17} = {(9, 153), (17, 17), (153, 9)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · -- Assume (a, b) satisfies the conditions: a > 0 ∧ b > 0 ∧ (1 / a : ℚ) + (1 / b : ℚ) = 2 / 17
      rintro ⟨ha, hb, heq⟩
      have h_eq1 : (a : ℚ) > (0 : ℚ) := by exact_mod_cast ha
      have h_eq2 : (b : ℚ) > (0 : ℚ) := by exact_mod_cast hb
      have h_eq3 : (a : ℚ) * (b : ℚ) > (0 : ℚ) := by nlinarith
      field_simp at heq
      have h_eq4 : (a : ℚ) * (b : ℚ) = (17 / 2) * (a + b : ℚ) := by
        nlinarith
      have h_eq5 : (2 * (a : ℚ) * (b : ℚ) : ℚ) = 17 * (a + b : ℚ) := by
        linarith [h_eq4]
      have h_eq6 : (2 * a * b : ℕ) = 17 * (a + b : ℕ) := by
        exact_mod_cast h_eq5
      have h2 : (2 * a * b : ℕ) = 17 * (a + b : ℕ) := h_eq6
      have h3 : a ≤ 153 := by
        by_contra h
        push_neg at h
        have h4 : b ≤ 8 := by
          nlinarith [h2, h]
        interval_cases b <;> omega
      have h4 : b ≤ 153 := by
        by_contra h
        push_neg at h
        have h5 : a ≤ 8 := by
          nlinarith [h2, h]
        interval_cases a <;> omega
      interval_cases a <;> omega
    · -- Show the three pairs satisfy the equation.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
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