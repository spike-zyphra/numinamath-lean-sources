import Mathlib

theorem number_theory_227582 {m n : ℕ} (h : m ≠ 0) (h' : n ≠ 0)
    (h'' : (1 / m : ℚ) + (1 / n : ℚ) = 1 / 2020) :
    ¬(Odd m ∧ Odd n) := by
  rintro ⟨h1, h2⟩
  have h_eq : (m : ℚ) * (n : ℚ) = 2020 * ((m : ℚ) + (n : ℚ)) := by
    have h_eq1 : (m : ℚ) ≠ 0 := by exact_mod_cast h
    have h_eq2 : (n : ℚ) ≠ 0 := by exact_mod_cast h'
    field_simp at h'' ⊢
    nlinarith
  have h_mod2_left : (m * n : ℕ) % 2 = 1 := by
    have h1' : m % 2 = 1 := by
      obtain ⟨k, hk⟩ := h1
      omega
    have h2' : n % 2 = 1 := by
      obtain ⟨k, hk⟩ := h2
      omega
    simp [Nat.mul_mod, h1', h2']
    all_goals omega
  have h_mod2_right : (2020 * (m + n) : ℕ) % 2 = 0 := by
    have h_2020 : 2020 % 2 = 0 := by norm_num
    simp [Nat.mul_mod, h_2020]
    all_goals omega
  have h_mod2_eq : (m * n : ℕ) % 2 = (2020 * (m + n) : ℕ) % 2 := by 
    have h_eq_nat : (m : ℚ) * (n : ℚ) = 2020 * ((m : ℚ) + (n : ℚ)) := h_eq
    have h1 : (m * n : ℕ) = (2020 * (m + n) : ℕ) := by 
      have h_eq_nat' : (m * n : ℕ) = (2020 * (m + n) : ℕ) := by
        exact_mod_cast h_eq_nat
      linarith
    omega
  omega