import Mathlib

theorem number_theory_235644 (p q r d : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime)
    (hqr : q = p + d) (hrr : r = p + 2 * d) (h1 : p > 3) (h2 : q > 3) (h3 : r > 3) :
    6 ∣ d := by 
  rcases hpqr with ⟨hp, hq, hr⟩
  have h8 : d % 2 = 0 := by 
    have hp2 : p % 2 = 1 := by 
      by_contra h
      push_neg at h
      have h10 : p % 2 = 0 := by omega
      have : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals linarith
      contradiction
    have hq2 : q % 2 = 1 := by 
      by_contra h
      push_neg at h
      have h12 : q % 2 = 0 := by omega
      have : ¬q.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
        all_goals linarith
      contradiction
    have h12 : (p + d) % 2 = 1 := by
      have h6 : q = p + d := by linarith [hqr]
      rw [h6] at *
      omega
    omega
  have h9 : d % 3 = 0 := by
    have hp2 : p % 3 = 1 ∨ p % 3 = 2 := by
      have h10 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases h10 with (h10 | h10 | h10)
      · -- contradiction: p % 3 = 0
        have h20 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
          all_goals linarith
        contradiction
      · left; exact h10
      · right; exact h10
    rcases hp2 with (h9 | h9)
    · -- p ≡ 1 (mod 3)
      have hq1 : q % 3 = 1 ∨ q % 3 = 2 := by
        have h10 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
        rcases h10 with (h10 | h10 | h10)
        · -- contradiction: q % 3 = 0
          have h20 : ¬q.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
            all_goals linarith
          contradiction
        · left; exact h10
        · right; exact h10
      have h11 : r % 3 = 1 ∨ r % 3 = 2 := by
        have h10 : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
        rcases h10 with (h10 | h10 | h10)
        · -- contradiction: r % 3 = 0
          have h20 : ¬r.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega)
            all_goals linarith
          contradiction
        · left; exact h10
        · right; exact h10
      have h12 : (p + 2 * d) % 3 = 1 ∨ (p + 2 * d) % 3 = 2 := by
        have h6 : r = p + 2 * d := by linarith [hrr]
        rw [h6] at *
        omega
      have h13 : (p + d) % 3 = 1 ∨ (p + d) % 3 = 2 := by
        have h6 : q = p + d := by linarith [hqr]
        rw [h6] at *
        omega
      omega
    · -- p ≡ 2 (mod 3)
      have hq1 : q % 3 = 1 ∨ q % 3 = 2 := by
        have h10 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
        rcases h10 with (h10 | h10 | h10)
        · -- contradiction: q % 3 = 0
          have h20 : ¬q.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
            all_goals linarith
          contradiction
        · left; exact h10
        · right; exact h10
      have h11 : r % 3 = 1 ∨ r % 3 = 2 := by
        have h10 : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
        rcases h10 with (h10 | h10 | h10)
        · -- contradiction: r % 3 = 0
          have h20 : ¬r.Prime := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega)
            all_goals linarith
          contradiction
        · left; exact h10
        · right; exact h10
      have h12 : (p + 2 * d) % 3 = 1 ∨ (p + 2 * d) % 3 = 2 := by
        have h6 : r = p + 2 * d := by linarith [hrr]
        rw [h6] at *
        omega
      have h13 : (p + d) % 3 = 1 ∨ (p + d) % 3 = 2 := by
        have h6 : q = p + d := by linarith [hqr]
        rw [h6] at *
        omega
      omega
  omega