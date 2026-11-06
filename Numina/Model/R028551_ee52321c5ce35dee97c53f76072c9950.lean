import Mathlib

theorem number_theory_15152 (a b : ℕ) (ha : a > 0) (hb : b > 0) (h1 : gcd a b = 1) (h2 : (a / b : ℚ) = 0.428125) : a + b = 457 := by
  have h3 : (a : ℚ) / (b : ℚ) = (137 : ℚ) / (320 : ℚ) := by
    have h6 : (a : ℚ) / (b : ℚ) = (0.428125 : ℚ) := by 
      simpa using h2
    rw [h6]
    norm_num
    <;> try { tauto }
  have h4 : a * 320 = 137 * b := by
    have h5 : (a : ℚ) * 320 = 137 * (b : ℚ) := by
      field_simp [show (b : ℚ) ≠ 0 by exact_mod_cast show (b : ℕ) ≠ 0 by omega] at h3 ⊢
      nlinarith
    exact_mod_cast h5
  have h6 : a = 137 := by
    have h7 : a * 320 = 137 * b := h4
    have h8 : a ∣ 137 * b := by
      use 320
      all_goals
      nlinarith
    have h9 : a ∣ 137 := by
      have h3a : Nat.gcd a b = 1 := h1
      have h3b : a ∣ 137 * b := h8
      have h11 : Nat.gcd a b = 1 := h1
      have h10 := Nat.Coprime.dvd_of_dvd_mul_right (show a.Coprime b by 
        rw [Nat.coprime_iff_gcd_eq_one] 
        exact h1
      ) h3b
      exact h10
    have h10 : a = 137 := by
      have h11 : a ≤ 137 := by
        exact Nat.le_of_dvd (by linarith) h9
      interval_cases a <;> omega
    omega
  have h7 : b = 320 := by
    have h3 : a * 320 = 137 * b := h4
    rw [h6] at h3
    nlinarith
  omega