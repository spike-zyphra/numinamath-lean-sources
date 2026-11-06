import Mathlib

theorem number_theory_113374 (a b : ℕ) (h₀ : a > b) (h₁ : Nat.Coprime a b) :
    Nat.gcd (a + b) (a - b) = 1 ∨ Nat.gcd (a + b) (a - b) = 2 := by
  have h2 : Nat.gcd (a + b) (a - b) ∣ (a + b) := by
    exact Nat.gcd_dvd_left (a + b) (a - b)
  have h3 : Nat.gcd (a + b) (a - b) ∣ (a - b) := by
    exact Nat.gcd_dvd_right (a + b) (a - b)
  have h4 : Nat.gcd (a + b) (a - b) ∣ (2 * a) := by
    have h5 : Nat.gcd (a + b) (a - b) ∣ (a + b) := by
      exact Nat.gcd_dvd_left (a + b) (a - b)
    have h6 : Nat.gcd (a + b) (a - b) ∣ (a - b) := by
      exact Nat.gcd_dvd_right (a + b) (a - b)
    have h7 : Nat.gcd (a + b) (a - b) ∣ ( (a + b) + (a - b) ) := Nat.dvd_add h5 h6
    have h8 : (a + b) + (a - b) = 2 * a := by omega
    rw [h8] at h7
    exact h7
  have h9 : Nat.gcd (a + b) (a - b) ∣ (2 * b) := by
    have h5 : Nat.gcd (a + b) (a - b) ∣ (a + b) := by
      exact Nat.gcd_dvd_left (a + b) (a - b)
    have h6 : Nat.gcd (a + b) (a - b) ∣ (a - b) := by
      exact Nat.gcd_dvd_right (a + b) (a - b)
    have h10 : Nat.gcd (a + b) (a - b) ∣ ( (a + b) - (a - b) ) := Nat.dvd_sub' h5 h6
    have h11 : (a + b) - (a - b) = 2 * b := by omega
    rw [h11] at h10
    exact h10
  have h12 : Nat.gcd (a + b) (a - b) ∣ 2 := by
    have h12 : Nat.gcd (a + b) (a - b) ∣ (2 * a) := h4
    have h13 : Nat.gcd (a + b) (a - b) ∣ (2 * b) := h9
    have h14 : Nat.gcd (a + b) (a - b) ∣ Nat.gcd (2 * a) (2 * b) := Nat.dvd_gcd h12 h13
    have h15 : Nat.gcd (2 * a) (2 * b) = 2 := by
      simp [Nat.gcd_mul_left, h₁]
    rw [h15] at h14
    exact h14
  have h16 : Nat.gcd (a + b) (a - b) = 1 ∨ Nat.gcd (a + b) (a - b) = 2 := by
    have h17 : Nat.gcd (a + b) (a - b) ∣ 2 := h12
    have h18 : Nat.gcd (a + b) (a - b) ≤ 2 := by 
      exact Nat.le_of_dvd (by norm_num) h17
    have h20 : Nat.gcd (a + b) (a - b) ≥ 1 := by
      have h21 : Nat.gcd (a + b) (a - b) > 0 := by 
        apply Nat.gcd_pos_of_pos_left
        omega
      omega
    interval_cases (Nat.gcd (a + b) (a - b)) <;> tauto
  exact h16