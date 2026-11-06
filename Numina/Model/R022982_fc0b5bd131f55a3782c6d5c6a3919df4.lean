import Mathlib

theorem number_theory_102427 (n : ℕ) :
    Nat.Coprime (3 * n + 2) (2 * n + 1) ∧
    IsSquare (Nat.lcm (3 * n + 2) (2 * n + 1) + Nat.lcm (3 * n + 2) (n + 1)) := by
  constructor
  · -- Prove that $a$ and $b$ are coprime
    have h1 : Nat.Coprime (3 * n + 2) (2 * n + 1) := by
      have h1 : Nat.gcd (3 * n + 2) (2 * n + 1) = 1 := by
        have h2 : Nat.gcd (3 * n + 2) (2 * n + 1) ∣ 3 * n + 2 := by
          exact Nat.gcd_dvd_left (3 * n + 2) (2 * n + 1)
        have h3 : Nat.gcd (3 * n + 2) (2 * n + 1) ∣ 2 * n + 1 := by
          exact Nat.gcd_dvd_right (3 * n + 2) (2 * n + 1)
        have h4 : Nat.gcd (3 * n + 2) (2 * n + 1) ∣ (2 * (3 * n + 2)) := by
          apply dvd_trans h2
          norm_num
          all_goals omega
        have h5 : Nat.gcd (3 * n + 2) (2 * n + 1) ∣ 3 * (2 * n + 1) := by
          apply dvd_trans h3
          norm_num
          all_goals omega
        have h6 : Nat.gcd (3 * n + 2) (2 * n + 1) ∣ (2 * (3 * n + 2) - 3 * (2 * n + 1)) := by
          apply Nat.dvd_sub'
          · apply dvd_trans h4
            norm_num
          · apply dvd_trans h5
            norm_num
        have h7 : 2 * (3 * n + 2) - 3 * (2 * n + 1) = 1 := by
          omega
        rw [h7] at h6
        have h8 : Nat.gcd (3 * n + 2) (2 * n + 1) = 1 := by
          exact Nat.eq_one_of_dvd_one h6
        linarith [h8]
      exact h1
    exact h1
  · -- Show that the number [a, b] + [a, c] is a perfect square
    have h3 : IsSquare (Nat.lcm (3 * n + 2) (2 * n + 1) + Nat.lcm (3 * n + 2) (n + 1)) := by
      have h1 : Nat.gcd (3 * n + 2) (2 * n + 1) = 1 := by
        have h1 : Nat.gcd (3 * n + 2) (2 * n + 1) = 1 := by
          have h2 : Nat.gcd (3 * n + 2) (2 * n + 1) ∣ 3 * n + 2 := by
            exact Nat.gcd_dvd_left (3 * n + 2) (2 * n + 1)
          have h3 : Nat.gcd (3 * n + 2) (2 * n + 1) ∣ 2 * n + 1 := by
            exact Nat.gcd_dvd_right (3 * n + 2) (2 * n + 1)
          have h4 : Nat.gcd (3 * n + 2) (2 * n + 1) ∣ (2 * (3 * n + 2)) := by
            apply dvd_trans h2
            norm_num
            all_goals omega
          have h5 : Nat.gcd (3 * n + 2) (2 * n + 1) ∣ 3 * (2 * n + 1) := by
            apply dvd_trans h3
            norm_num
            all_goals omega
          have h6 : Nat.gcd (3 * n + 2) (2 * n + 1) ∣ (2 * (3 * n + 2) - 3 * (2 * n + 1)) := by
            apply Nat.dvd_sub'
            · apply dvd_trans h4
              norm_num
            · apply dvd_trans h5
              norm_num
          have h7 : 2 * (3 * n + 2) - 3 * (2 * n + 1) = 1 := by
            omega
          rw [h7] at h6
          have h8 : Nat.gcd (3 * n + 2) (2 * n + 1) = 1 := by
            exact Nat.eq_one_of_dvd_one h6
          linarith [h8]
        linarith [h1]
      have h8 : Nat.gcd (3 * n + 2) (n + 1) = 1 := by
        have h2 : Nat.gcd (3 * n + 2) (n + 1) ∣ 3 * n + 2 := by
          exact Nat.gcd_dvd_left (3 * n + 2) (n + 1)
        have h3 : Nat.gcd (3 * n + 2) (n + 1) ∣ n + 1 := by
          exact Nat.gcd_dvd_right (3 * n + 2) (n + 1)
        have h4 : Nat.gcd (3 * n + 2) (n + 1) ∣ 3 * (n + 1) := by
          apply dvd_trans h3
          norm_num
          all_goals omega
        have h7 : Nat.gcd (3 * n + 2) (n + 1) ∣ (3 * (n + 1)) := h4
        have h5 : Nat.gcd (3 * n + 2) (n + 1) ∣ (3 * (n + 1) - (3 * n + 2)) := by
          apply Nat.dvd_sub'
          · exact h7
          · apply dvd_trans h2
            norm_num
            all_goals omega
        have h9 : 3 * (n + 1) - (3 * n + 2) = 1 := by
          omega
        rw [h9] at h5
        have h10 : Nat.gcd (3 * n + 2) (n + 1) = 1 := by
          exact Nat.eq_one_of_dvd_one h5
        linarith [h10]
      have h9 : Nat.lcm (3 * n + 2) (2 * n + 1) = (3 * n + 2) * (2 * n + 1) := by
        rw [Nat.lcm]
        rw [h1]
        <;> simp [Nat.mul_comm]
      have h10 : Nat.lcm (3 * n + 2) (n + 1) = (3 * n + 2) * (n + 1) := by
        rw [Nat.lcm]
        rw [h8]
        <;> simp [Nat.mul_comm]
      rw [h9, h10]
      use 3 * n + 2
      all_goals ring_nf <;> omega
    exact h3