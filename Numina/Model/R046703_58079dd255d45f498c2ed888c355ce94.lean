import Mathlib

theorem number_theory_6390
    (a b c : ℕ)
    (hab : Nat.Coprime a b)
    (hc : c ∣ a + b) :
    Nat.Coprime c a ∧ Nat.Coprime c b := by
  constructor
  · -- Show that Nat.Coprime c a
    rw [Nat.coprime_iff_gcd_eq_one]
    have h1 : Nat.gcd c a ∣ c := by
      exact Nat.gcd_dvd_left c a
    have h2 : Nat.gcd c a ∣ a := by
      exact Nat.gcd_dvd_right c a
    have h3 : Nat.gcd c a ∣ b := by
      have h4 : Nat.gcd c a ∣ (a + b) := by
        have h5 : Nat.gcd c a ∣ c := h1
        have h6 : c ∣ (a + b) := hc
        have h7 : Nat.gcd c a ∣ (a + b) := dvd_trans h5 h6
        exact h7
      have h8 : Nat.gcd c a ∣ a := h2
      have h9 : Nat.gcd c a ∣ ((a + b) - a) := by
        apply Nat.dvd_sub'
        · exact h4
        · exact h8
      have h10 : (a + b) - a = b := by
        omega
      rw [h10] at h9
      exact h9
    have h6 : Nat.gcd c a ∣ 1 := by 
      have h7 : Nat.gcd c a ∣ a := h2
      have h8 : Nat.gcd c a ∣ b := h3
      have h9 : Nat.gcd c a ∣ Nat.gcd a b := Nat.dvd_gcd h7 h8
      have h10 : Nat.gcd a b = 1 := hab
      rw [h10] at h9
      exact h9
    have h1 : c ≠ 0 ∨ a ≠ 0 := by 
      by_contra h
      push_neg at h
      have hc1 : c = 0 := h.1
      have h2 : a = 0 := h.2
      rw [hc1, h2] at hc
      have h3 : b = 0 := by
        simp at hc ⊢
        all_goals omega
      rw [h2, h3] at hab
      norm_num [Nat.Coprime] at hab
      all_goals tauto
    have h2 : Nat.gcd c a ≥ 1 := by
      by_contra h
      push_neg at h
      have h3 : Nat.gcd c a = 0 := by
        omega
      have h4 : c = 0 ∧ a = 0 := by 
        rw [Nat.gcd_eq_zero_iff] at h3
        exact h3
      have h5 : c = 0 := h4.1
      have h6 : a = 0 := h4.2
      have h8 : c = 0 ∨ a = 0 := by 
        simp [h5, h6]
      tauto
    have h7 : Nat.gcd c a ∣ 1 := h6
    have h8 : Nat.gcd c a = 1 := by
      have h9 : Nat.gcd c a ∣ 1 := h7
      have h10 : Nat.gcd c a ≤ 1 := by 
        exact Nat.le_of_dvd (show 0 < 1 by norm_num) h9
      omega
    exact h8
  · -- Show that Nat.Coprime c b
    rw [Nat.coprime_iff_gcd_eq_one]
    have h1 : Nat.gcd c b ∣ c := by
      exact Nat.gcd_dvd_left c b
    have h2 : Nat.gcd c b ∣ b := by
      exact Nat.gcd_dvd_right c b
    have h3 : Nat.gcd c b ∣ a := by
      have h4 : Nat.gcd c b ∣ (a + b) := by
        have h5 : Nat.gcd c b ∣ c := h1
        have h6 : c ∣ (a + b) := hc
        have h7 : Nat.gcd c b ∣ (a + b) := dvd_trans h5 h6
        exact h7
      have h8 : Nat.gcd c b ∣ b := h2
      have h9 : Nat.gcd c b ∣ ((a + b) - b) := by
        apply Nat.dvd_sub'
        · exact h4
        · exact h8
      have h10 : (a + b) - b = a := by
        omega
      rw [h10] at h9
      exact h9
    have h6 : Nat.gcd c b ∣ 1 := by 
      have h7 : Nat.gcd c b ∣ a := h3
      have h8 : Nat.gcd c b ∣ b := h2
      have h9 : Nat.gcd c b ∣ Nat.gcd a b := Nat.dvd_gcd h7 h8
      have h10 : Nat.gcd a b = 1 := hab
      rw [h10] at h9
      exact h9
    have h1 : c ≠ 0 ∨ b ≠ 0 := by 
      by_contra h
      push_neg at h
      have hc1 : c = 0 := h.1
      have h2 : b = 0 := h.2
      rw [hc1, show b = 0 by omega] at hc
      have h3 : a = 0 := by
        simp at hc ⊢
        all_goals omega
      rw [show a = 0 by omega, show b = 0 by omega] at hab
      norm_num [Nat.Coprime] at hab
      all_goals tauto
    have h2 : Nat.gcd c b ≥ 1 := by
      by_contra h
      push_neg at h
      have h3 : Nat.gcd c b = 0 := by
        omega
      have h4 : c = 0 ∧ b = 0 := by 
        rw [Nat.gcd_eq_zero_iff] at h3
        exact h3
      have h5 : c = 0 := h4.1
      have h6 : b = 0 := h4.2
      have h8 : c = 0 ∨ b = 0 := by 
        simp [h5, h6]
      tauto
    have h7 : Nat.gcd c b ∣ 1 := h6
    have h8 : Nat.gcd c b = 1 := by
      have h9 : Nat.gcd c b ∣ 1 := h7
      have h10 : Nat.gcd c b ≤ 1 := by 
        exact Nat.le_of_dvd (show 0 < 1 by norm_num) h9
      omega
    exact h8