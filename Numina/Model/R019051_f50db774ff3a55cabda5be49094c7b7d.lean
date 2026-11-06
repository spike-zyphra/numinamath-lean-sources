import Mathlib

theorem number_theory_178125 (p n : ℕ) (hp : Nat.Prime p) (hn : 1 ≤ n)
    (hpn : p ≠ 3) :
    ¬Nat.Prime ((3 * n - 1) * p^2 + 1) := by
  have hp1 : p ≥ 2 := Nat.Prime.two_le hp
  have hp2 : p % 3 = 1 ∨ p % 3 = 2 := by
    by_contra h
    push_neg at h
    have : p % 3 = 0 := by 
      omega
    have : 3 ∣ p := by 
      omega
    have h1 : p > 3 := by
      by_contra h
      push_neg at h
      interval_cases p <;> try { contradiction } <;> norm_num at hp hp1 hpn
      all_goals omega
    have h4 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals omega
    contradiction
  rcases hp2 with (h | h)
  · -- p ≡ 1 [MOD 3]
    have hp1' : p % 3 = 1 := h
    have hp2' : p^2 % 3 = 1 := by
      simp [Nat.pow_mod, hp1']
    have eq1 : ( (3 * n - 1) * p^2 + 1 ) % 3 = 0 := by
      have h6 : p^2 % 3 = 1 := hp2'
      have h14 : (3 * n - 1) * p^2 % 3 = 2 := by
        have h15 : (3 * n - 1) % 3 = 2 := by 
          omega
        have h16 : p^2 % 3 = 1 := hp2'
        simp [Nat.mul_mod, h15, h16]
        all_goals omega
      omega
    have h11 : (3 * n - 1) * p^2 + 1 > 3 := by
      have hp2 : p ≥ 2 := by linarith [hp1]
      have hp22 : p^2 ≥ 4 := by
        nlinarith
      have h12 : 3 * n ≥ 3 := by
        omega
      have h13 : 3 * n - 1 ≥ 2 := by
        omega
      have h14 : (3 * n - 1) * p^2 ≥ 8 := by
        nlinarith [h13, hp22]
      omega
    have h3 : ¬Nat.Prime ((3 * n - 1) * p^2 + 1) := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ ( (3 * n - 1) * p^2 + 1 ) by omega )
      all_goals linarith
      all_goals linarith
    exact h3
  · -- p ≡ 2 [MOD 3]
    have hp1' : p % 3 = 2 := h
    have hp2' : p^2 % 3 = 1 := by
      simp [Nat.pow_mod, hp1']
    have eq1 : ( (3 * n - 1) * p^2 + 1 ) % 3 = 0 := by
      have h6 : p^2 % 3 = 1 := hp2'
      have h14 : (3 * n - 1) * p^2 % 3 = 2 := by
        have h15 : (3 * n - 1) % 3 = 2 := by 
          omega
        have h16 : p^2 % 3 = 1 := hp2'
        simp [Nat.mul_mod, h15, h16]
        all_goals omega
      omega
    have h11 : (3 * n - 1) * p^2 + 1 > 3 := by
      have hp2 : p ≥ 2 := by linarith [hp1]
      have hp22 : p^2 ≥ 4 := by
        nlinarith
      have h12 : 3 * n ≥ 3 := by
        omega
      have h13 : 3 * n - 1 ≥ 2 := by
        omega
      have h14 : (3 * n - 1) * p^2 ≥ 8 := by
        nlinarith [h13, hp22]
      omega
    have h3 : ¬Nat.Prime ((3 * n - 1) * p^2 + 1) := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ ( (3 * n - 1) * p^2 + 1 ) by omega )
      all_goals linarith
      all_goals linarith
    exact h3