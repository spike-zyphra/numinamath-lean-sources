import Mathlib

theorem number_theory_289508 (a b c : ℕ) (h₀ : b = a + 1) (h₁ : c = b + 1) :
    Nat.Coprime (b^2 - a^2) (c^2 - b^2) := by
  have h2 : c = a + 2 := by
    rw [h₁, h₀]
    all_goals omega
  have eq1 : b^2 - a^2 = 2 * a + 1 := by 
    rw [h₀]
    ring_nf
    <;> omega 
  have eq2 : c^2 - b^2 = 2 * a + 3 := by
    rw [h2, h₀] 
    ring_nf 
    <;> omega 
  rw [eq1, eq2]
  have h3 : Nat.Coprime (2 * a + 1) (2 * a + 3) := by
    have h6 : Nat.gcd (2 * a + 1) (2 * a + 3) ∣ (2 * a + 1) := by 
      apply Nat.gcd_dvd_left 
    have h7 : Nat.gcd (2 * a + 1) (2 * a + 3) ∣ (2 * a + 3) := by 
      apply Nat.gcd_dvd_right 
    have h8 : Nat.gcd (2 * a + 1) (2 * a + 3) ∣ ((2 * a + 3) - (2 * a + 1)) := by 
      apply Nat.dvd_sub' 
      · exact h7 
      · exact h6 
    have h9 : ((2 * a + 3) - (2 * a + 1)) = 2 := by 
      omega 
    rw [h9] at h8
    have h10 : Nat.gcd (2 * a + 1) (2 * a + 3) = 1 := by
      have h11 : Nat.gcd (2 * a + 1) (2 * a + 3) ∣ 2 := h8 
      have h12 : Nat.gcd (2 * a + 1) (2 * a + 3) ∣ (2 * a + 1) := h6 
      have h14 : Nat.gcd (2 * a + 1) (2 * a + 3) ≤ 2 := by 
        exact Nat.le_of_dvd (by norm_num) h11 
      interval_cases (Nat.gcd (2 * a + 1) (2 * a + 3)) <;> norm_num at h11 h12 
      all_goals 
        omega 
    rw [Nat.coprime_iff_gcd_eq_one] 
    exact h10 
  exact h3