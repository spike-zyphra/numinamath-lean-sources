import Mathlib

theorem number_theory_91016 (p : ℕ) (hp : Nat.Prime p) (h : 5 < p) :
    ∃ n : ℕ, 0 < n ∧ (p ^ n) % 1000 = 1 := by
  have h1 : p > 5 := h
  have h2 : p % 2 ≠ 0 := by
    by_contra h2
    have h3 : 2 ∣ p := by
      omega
    have h4 : p ≠ 2 := by
      linarith
    have h3 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by linarith) (by linarith)
    tauto
  have h3 : p % 5 ≠ 0 := by
    by_contra h3
    have h4 : 5 ∣ p := by
      omega
    have h5 : p ≠ 5 := by
      linarith
    have h6 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega) (by linarith) (by linarith)
    tauto
  have h4 : Nat.gcd p 1000 = 1 := by
    have h30 : Nat.gcd p 1000 ∣ p := by
      exact Nat.gcd_dvd_left p 1000
    have h31 : Nat.gcd p 1000 ∣ 1000 := by
      exact Nat.gcd_dvd_right p 1000
    have h37 : Nat.gcd p 1000 = 1 ∨ Nat.gcd p 1000 = p := by
      have h42 : Nat.gcd p 1000 ∣ p := h30
      have h43 : Nat.Prime p := hp
      have h44 : Nat.gcd p 1000 = 1 ∨ Nat.gcd p 1000 = p := by
        apply (Nat.dvd_prime hp).mp
        exact h30
      tauto
    rcases h37 with h38 | h39
    · 
      tauto
    · 
      -- Now if gcd p 1000 = p
      have h40 : p ∣ 1000 := by
        have h399 : p = Nat.gcd p 1000 := by 
          omega
        have h410 : Nat.gcd p 1000 ∣ 1000 := h31
        rw [show Nat.gcd p 1000 = p by omega] at h410
        exact h410
      have h43 : p ∣ 2 ∨ p ∣ 5 := by
        have h44 : p ∣ 1000 := h40
        have h45 : p ∣ 2 ^ 3 * 5 ^ 3 := by
          norm_num at h44 ⊢
          exact h44
        have h48 : p ∣ 2 ^ 3 ∨ p ∣ 5 ^ 3 := by
          apply (Nat.Prime.dvd_mul hp).mp at h45
          tauto
        rcases h48 with h49 | h50
        · 
          have h51 : p ∣ 2 := by
            have h52 : p ∣ 2 ^ 3 := h49
            have h53 : p ∣ 2 := by
              apply Nat.Prime.dvd_of_dvd_pow hp
              exact h52
            exact h53
          tauto
        · 
          have h54 : p ∣ 5 := by
            have h55 : p ∣ 5 ^ 3 := h50
            have h56 : p ∣ 5 := by
              apply Nat.Prime.dvd_of_dvd_pow hp
              exact h55
            exact h56
          tauto
      rcases h43 with h44 | h45
      · 
        have h46 : p ≤ 2 := by
          exact Nat.le_of_dvd (by linarith) h44
        omega
      · 
        have h47 : p ≤ 5 := by
          exact Nat.le_of_dvd (by linarith) h45
        omega
  have h5 : (p ^ 400) % 1000 = 1 := by
    have h7 : p.Coprime 1000 := by
      rw [Nat.coprime_iff_gcd_eq_one]
      exact h4
    have h8 : p ^ (Nat.totient 1000) ≡ 1 [MOD 1000] := by
      apply Nat.ModEq.pow_totient
      exact h7
    have h9 : Nat.totient 1000 = 400 := by
      native_decide
    rw [h9] at h8
    exact h8
  refine' ⟨400, by norm_num, h5⟩