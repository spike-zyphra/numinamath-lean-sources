import Mathlib

theorem number_theory_95154 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ Nat.Coprime x y ∧ (x + 1 : ℚ) / (y + 1) = 1.1 * x / y}.ncard = 1 := by
  have h₁ : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ Nat.Coprime x y ∧ (x + 1 : ℚ) / (y + 1) = 1.1 * x / y} = {(5, 11)} := by
    ext ⟨x, y⟩
    simp [- one_div]
    constructor
    · -- Assume (x, y) is in the set
      rintro ⟨hx, hy, h_coprime, h_eq⟩
      have h_eq1 : ((x : ℚ) + 1) / ((y : ℚ) + 1) = 1.1 * ((x : ℚ) / (y : ℚ)) := by
        field_simp at h_eq ⊢
        <;> nlinarith 
      have h_eq2 : (x : ℚ) * (y + 11 : ℚ) = 10 * (y : ℚ) := by
        field_simp at h_eq1 ⊢
        nlinarith
      have h_eq3 : (x : ℕ) * (y + 11 : ℕ) = 10 * (y : ℕ) := by
        have h1 : (x : ℚ) * (y + 11 : ℚ) = 10 * (y : ℚ) := h_eq2
        exact_mod_cast h1
      have h3 : x ≤ 10 * y := by
        nlinarith
      have h4 : x ∣ 10 * y := by
        use y + 11
        nlinarith [h_eq3]
      have h5 : x ∣ 10 := by
        have h6 : x ∣ 10 * y := h4
        have h7 : x.Coprime y := by exact h_coprime
        have h8 : x ∣ 10 := by 
          apply Nat.Coprime.dvd_of_dvd_mul_right h7 h6
        exact h8
      have h6 : x ≤ 10 := by
        exact Nat.le_of_dvd (show 0 < 10 by norm_num) h5
      interval_cases x <;> omega
    · -- Show that (5, 11) is in the set
      rintro ⟨rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
  rw [h₁]
  simp [Set.ncard_singleton]