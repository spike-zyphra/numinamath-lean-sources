import Mathlib

theorem number_theory_39140 (r : ℝ) (hr : r > 0) :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a.Prime ∧ b.Prime ∧ c.Prime ∧ a^2 + b^2 = c^2 ∧
      (a + b - c) * (b + c - a) * (c + a - b) = 2 * r * (a + b + c)}.ncard = 0 ∨
    ∃ k, {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a.Prime ∧ b.Prime ∧ c.Prime ∧ a^2 + b^2 = c^2 ∧
      (a + b - c) * (b + c - a) * (c + a - b) = 2 * r * (a + b + c)}.ncard = 2 ^ k := by
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a.Prime ∧ b.Prime ∧ c.Prime ∧ a^2 + b^2 = c^2 ∧
    (a + b - c) * (b + c - a) * (c + a - b) = 2 * r * (a + b + c)} = ∅ := by
    ext ⟨a, b, c⟩
    simp
    intro ha hb hc ha1 hb1 hc1 h1 h2
    have h3 : a % 2 = 1 ∨ a % 2 = 0 := by omega
    have h4 : b % 2 = 1 ∨ b % 2 = 0 := by omega
    have h5 : c % 2 = 1 ∨ c % 2 = 0 := by omega
    have h6 : a % 2 = 1 ∨ a = 2 := by
      by_cases ha2 : a > 2
      · 
        have h8 : a % 2 = 1 := by
          by_contra h
          push_neg at h
          have h9 : a % 2 = 0 := by omega
          have h10 : 2 ∣ a := by
            omega
          have h11 : ¬a.Prime := by
            apply Nat.not_prime_of_dvd_of_lt h10
            all_goals omega
          tauto
        omega
      · 
        have h10 : a ≤ 2 := by omega
        interval_cases a <;> try tauto
    have h7 : b % 2 = 1 ∨ b = 2 := by
      by_cases hb2 : b > 2
      · 
        have h8 : b % 2 = 1 := by
          by_contra h
          push_neg at h
          have h9 : b % 2 = 0 := by omega
          have h10 : 2 ∣ b := by
            omega
          have h11 : ¬b.Prime := by
            apply Nat.not_prime_of_dvd_of_lt h10
            all_goals omega
          tauto
        omega
      · 
        have h10 : b ≤ 2 := by omega
        interval_cases b <;> try tauto
    have h8 : c % 2 = 1 ∨ c = 2 := by
      by_cases hc2 : c > 2
      · 
        have h9 : c % 2 = 1 := by
          by_contra h
          push_neg at h
          have h10 : c % 2 = 0 := by omega
          have h11 : 2 ∣ c := by
            omega
          have h12 : ¬c.Prime := by
            apply Nat.not_prime_of_dvd_of_lt h11
            all_goals omega
          tauto
        omega
      · 
        have h13 : c ≤ 2 := by omega
        interval_cases c <;> try tauto
    rcases h6 with (ha2 | ha2)
    · 
      rcases h7 with (hb2 | hb2)
      · 
        rcases h8 with (hc2 | hc2)
        · 
          have h9 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
            omega
          have h10 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by
            omega
          have h11 : a ^ 2 % 8 = 1 := by
            rcases h9 with (h | h | h | h) <;> simp [Nat.pow_mod, h]
          have h12 : b ^ 2 % 8 = 1 := by
            rcases h10 with (h | h | h | h) <;> simp [Nat.pow_mod, h]
          have h13 : c ^ 2 % 8 = 2 := by
            omega
          have h14 : c ^ 2 % 8 = 0 ∨ c ^ 2 % 8 = 1 ∨ c ^ 2 % 8 = 4 := by
            have h15 : c % 8 = 0 ∨ c % 8 = 1 ∨ c % 8 = 2 ∨ c % 8 = 3 ∨ c % 8 = 4 ∨ c % 8 = 5 ∨ c % 8 = 6 ∨ c % 8 = 7 := by 
              omega
            rcases h15 with (h | h | h | h | h | h | h | h) <;> simp [Nat.pow_mod, h]
          omega
        · 
          have h14 : c = 2 := by
            omega
          rw [show c = 2 by omega] at h1
          have h15 : a ^ 2 + b ^ 2 = 4 := by
            nlinarith
          have h16 : a ≤ 2 := by
            nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ)]
          have h17 : b ≤ 2 := by
            nlinarith [sq_nonneg (a : ℕ), sq_nonneg (b : ℕ)]
          interval_cases a <;> interval_cases b <;> norm_num at h15 ha1 hb1 h1
      · 
        have h14 : b = 2 := by
          omega
        rw [show b = 2 by omega] at h1
        have h15 : a ^ 2 + 4 = c ^ 2 := by
          nlinarith
        have h16 : (c : ℕ) > (a : ℕ) := by
          nlinarith
        have h17 : c ≤ a + 2 := by
          nlinarith [sq_nonneg (c - (a + 1) : ℤ)]
        have h18 : c = a + 1 ∨ c = a + 2 := by
          omega
        rcases h18 with (h18 | h18)
        · 
          have h19 : (c : ℕ) = a + 1 := by
            omega
          rw [show c = a + 1 by omega] at h15
          have h20 : a ≤ 1 := by
            nlinarith [sq_nonneg (a : ℕ)]
          have h21 : a > 1 := by
            by_contra h
            push_neg at h
            have h22 : a ≤ 1 := by
              linarith
            interval_cases a <;> norm_num at ha1 h15 h22
          nlinarith
        · 
          have h23 : (c : ℕ) = a + 2 := by
            omega
          rw [show c = a + 2 by omega] at h15
          have h24 : a = 0 := by
            nlinarith
          nlinarith
    · 
      have h14 : a = 2 := by
        omega
      rw [show a = 2 by omega] at h1
      have h15 : 4 + b ^ 2 = c ^ 2 := by
        nlinarith
      have h16 : (c : ℕ) > (b : ℕ) := by
        nlinarith
      have h17 : c ≤ b + 2 := by
        nlinarith [sq_nonneg (c - (b + 1) : ℤ)]
      have h18 : c = b + 1 ∨ c = b + 2 := by
        omega
      rcases h18 with (h18 | h18)
      · 
        have h19 : (c : ℕ) = b + 1 := by
          omega
        rw [show c = b + 1 by omega] at h15
        have h20 : b ≤ 1 := by
          nlinarith [sq_nonneg (b : ℕ)]
        have h21 : b > 1 := by
          by_contra h
          push_neg at h
          have h22 : b ≤ 1 := by
            linarith
          interval_cases b <;> norm_num at hb1 h15 h22
        nlinarith
      · 
        have h23 : (c : ℕ) = b + 2 := by
          omega
        rw [show c = b + 2 by omega] at h15
        have h24 : b = 0 := by
          nlinarith
        nlinarith
  rw [h1]
  simp