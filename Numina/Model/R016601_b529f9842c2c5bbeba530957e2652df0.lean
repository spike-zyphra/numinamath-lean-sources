import Mathlib

theorem number_theory_4669 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ (2 / 15 : ℚ) = 1 / a + 1 / b ∧ a ≤ b}.ncard = 5 := by
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ (2 / 15 : ℚ) = 1 / a + 1 / b ∧ a ≤ b} = {(8, 120), (9, 45), (10, 30), (12, 20), (15, 15)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · -- Assume (a, b) satisfies the conditions
      rintro ⟨ha, hb, heq, hab⟩
      have h2 : (a : ℚ) > 0 := by exact_mod_cast ha
      have h3 : (b : ℚ) > 0 := by exact_mod_cast hb
      have h_eq : (2 : ℚ) * (a : ℚ) * (b : ℚ) = 15 * ((a : ℚ) + (b : ℚ)) := by
        field_simp at heq ⊢
        nlinarith
      have h_eq_nat : 2 * a * b = 15 * (a + b) := by
        exact_mod_cast h_eq
      have h3 : a ≤ b := hab
      have h4 : a ≤ 120 := by
        by_contra h
        push_neg at h
        have h5 : b < 8 := by
          nlinarith [show 2 * a * b = 15 * (a + b) from h_eq_nat]
        interval_cases b <;> nlinarith
      have h5 : b ≤ 120 := by
        by_contra h
        push_neg at h
        have h6 : a < 8 := by
          nlinarith [show 2 * a * b = 15 * (a + b) from h_eq_nat]
        interval_cases a <;> nlinarith
      interval_cases a <;> omega
    · -- Show that each pair in the finite set satisfies the conditions.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (8, 120)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (9, 45)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (10, 30)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (12, 20)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (15, 15)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }