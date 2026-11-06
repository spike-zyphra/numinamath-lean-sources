import Mathlib

theorem number_theory_318189 (a b : ℕ) (_ : 0 < a) (h₀ : 0 < b)
    (h₁ : a - b = 120 ∨ b - a = 120) (h₂ : Nat.lcm a b = 105 * Nat.gcd a b) :
    max a b = 225 := by
  rcases h₁ with h₁ | h₁
  · -- Assume a - b = 120, so a = b + 120
    have h3 : a = b + 120 := by
      omega
    rw [h3] at h₂
    have h4 : b ≤ 1231 := by
      by_contra h
      push_neg at h
      have h5 : Nat.gcd (b + 120) b ∣ b := by
        apply Nat.gcd_dvd_right
      have h6 : Nat.gcd (b + 120) b ∣ (b + 120) := by
        apply Nat.gcd_dvd_left
      have h7 : Nat.gcd (b + 120) b ∣ 120 := by
        have h8 : Nat.gcd (b + 120) b ∣ (b + 120) := h6
        have h9 : Nat.gcd (b + 120) b ∣ b := h5
        have h10 : Nat.gcd (b + 120) b ∣ ((b + 120) - b) := by
          apply Nat.dvd_sub'
          · exact h8
          · exact h9
        have h11 : ((b + 120) - b) = 120 := by
          omega
        rw [h11] at h10
        exact h10
      have h13 : Nat.gcd (b + 120) b ≤ 120 := by
        exact Nat.le_of_dvd (by linarith) h7
      have h9 : (b + 120) * b = 105 * (Nat.gcd (b + 120) b) ^ 2 := by
        calc
          (b + 120) * b = Nat.gcd (b + 120) b * Nat.lcm (b + 120) b := by
            rw [Nat.gcd_mul_lcm (b + 120) b]
          _ = Nat.gcd (b + 120) b * (105 * Nat.gcd (b + 120) b) := by
            rw [h₂]
            <;> ring
          _ = 105 * (Nat.gcd (b + 120) b) ^ 2 := by
            ring
      nlinarith [h9, h13, sq_nonneg (b + 60)]
    interval_cases b <;> norm_num [Nat.lcm, Nat.gcd] at h₂ ⊢
    <;> omega
  · -- Assume b - a = 120, so b = a + 120
    have h4 : b = a + 120 := by
      omega
    rw [h4] at h₂
    have h5 : a ≤ 1231 := by
      by_contra h
      push_neg at h
      have h5 : Nat.gcd a (a + 120) ∣ a := by
        apply Nat.gcd_dvd_left
      have h6 : Nat.gcd a (a + 120) ∣ (a + 120) := by
        apply Nat.gcd_dvd_right
      have h7 : Nat.gcd a (a + 120) ∣ 120 := by
        have h8 : Nat.gcd a (a + 120) ∣ (a + 120) := h6
        have h9 : Nat.gcd a (a + 120) ∣ a := h5
        have h10 : Nat.gcd a (a + 120) ∣ ((a + 120) - a) := by
          apply Nat.dvd_sub'
          · exact h8
          · exact h9
        have h11 : ((a + 120) - a) = 120 := by
          omega
        rw [h11] at h10
        exact h10
      have h12 : Nat.gcd a (a + 120) ≤ 120 := by
        exact Nat.le_of_dvd (by linarith) h7
      have h9 : a * (a + 120) = 105 * (Nat.gcd a (a + 120)) ^ 2 := by
        calc
          a * (a + 120) = Nat.gcd a (a + 120) * Nat.lcm a (a + 120) := by
            rw [Nat.gcd_mul_lcm a (a + 120)]
          _ = Nat.gcd a (a + 120) * (105 * Nat.gcd a (a + 120)) := by
            rw [h₂]
            <;> ring
          _ = 105 * (Nat.gcd a (a + 120)) ^ 2 := by
            ring
      nlinarith [h9, h12, sq_nonneg (a + 60)]
    interval_cases a <;> norm_num [Nat.lcm, Nat.gcd] at h₂ ⊢
    <;> omega