import Mathlib


theorem number_theory_215307 (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)  (h : p ^ q = r - 1) : p = 2 ∧ q = 2 ∧ r = 5 := by
  have h1 : q ≥ 2 := Nat.Prime.two_le hq
  have h2 : p ≥ 2 := Nat.Prime.two_le hp
  have h3 : r ≥ 2 := Nat.Prime.two_le hr

  by_cases h4 : p > 2
  · -- If p > 2, then p must be odd.
    have h5 : p % 2 = 1 := by
      by_contra h6
      push_neg at h6
      have h7 : p % 2 = 0 := by omega
      have h8 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
      contradiction

    have h10 : r % 2 = 0 := by
      have h11 : p % 2 = 1 := h5
      have h12 : (p ^ q) % 2 = 1 := by
        have : ∀ m : ℕ, (p ^ (m + 1)) % 2 = 1 := by
          intro m
          induction m with
          | zero =>
            simp [h11]
          | succ m ih =>
            simp [Nat.pow_succ, Nat.mul_mod, h11] at ih ⊢
            all_goals omega
        have h15 : q ≥ 1 := by
          have h16 : q ≥ 2 := h1
          omega
        specialize this (q - 1)
        have h16 : q - 1 + 1 = q := by
          omega
        rw [h16] at this
        omega
      omega

    by_cases h13 : r > 2
    · -- If r > 2, then r is not 2.
      have h14 : r % 2 = 0 := h10
      have h15 : ¬r.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ r by omega) (by omega) (by omega)
      contradiction
    · -- r ≤ 2.
      have h18 : r ≤ 2 := by omega
      have h19 : r = 2 := by
        interval_cases r <;> tauto
      rw [h19] at h
      have h17 : p ^ q ≤ 1 := by
        omega
      have h18 : p ^ q ≥ 4 := by
        have h19 : p ≥ 2 := hp.two_le
        have h20 : q ≥ 2 := hq.two_le
        have h21 : p ^ q ≥ 4 := by
          have h22 : p ^ 2 ≥ 4 := by
            nlinarith
          have h23 : q ≥ 2 := hq.two_le
          have h24 : p ^ q ≥ p ^ 2 := by
            apply Nat.pow_le_pow_of_le_right
            all_goals linarith
          nlinarith
        linarith
      omega

  · -- If p ≤ 2, then p = 2.
    have h19 : p = 2 := by
      interval_cases p <;> try tauto

    rw [h19] at h
    by_cases h34 : q > 2
    · -- If q > 2, then q must be odd.
      have h37 : q % 2 = 1 := by
        by_contra h40
        push_neg at h40
        have h41 : q % 2 = 0 := by omega
        have h42 : ¬q.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) (by omega) (by omega)
        contradiction

      have h39 : (2 : ℕ) ^ q % 3 = 2 := by
        have h40 : ∀ (k : ℕ), (2 : ℕ) ^ (2 * k + 1) % 3 = 2 := by
          intro k
          induction k with
          | zero =>
            norm_num
          | succ k ih =>
            simp [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, pow_two] at ih ⊢
            all_goals omega
        have h41 : ∃ k : ℕ, q = 2 * k + 1 := by
          use (q - 1) / 2
          omega
        rcases h41 with ⟨k, hk⟩
        rw [hk] 
        apply h40 k

      have h43 : r % 3 = 0 := by 
        have eq1 : 2 ^ q = r - 1 := by 
          omega
        have eq2 : 2 ^ q % 3 = 2 := h39
        omega

      have h44 : r ≤ 3 := by
        by_contra h45
        push_neg at h45
        have h47 : r % 3 = 0 := h43
        have h48 : r > 3 := by linarith
        have h49 : ¬r.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ r by omega) (by omega) (by omega)
        contradiction

      have h45 : r ≤ 3 := h44
      have h48 : 2 ^ q ≤ 2 := by
        omega

      have h47 : q ≤ 1 := by
        by_contra h48
        push_neg at h48
        have h49 : q > 1 := by omega
        have h50 : 2 ^ q ≥ 4 := by
          have h51 : q ≥ 2 := by omega
          have : 2 ^ q ≥ 4 := by
            have h77 : 2 ^ 2 = 4 := by norm_num
            have h78 : 2 ^ q ≥ 2 ^ 2 := by
              apply Nat.pow_le_pow_of_le_right (by linarith) h51
            linarith [h77, h78]
          linarith
        omega

      omega

    · -- If q ≤ 2, then q = 2.
      have h44 : q ≤ 2 := by omega
      have h45 : q = 2 := by 
        interval_cases q <;> try tauto
      rw [h45] at h
      have h46 : r = 5 := by
        omega
      constructor
      · -- p = 2
        omega
      constructor
      · -- q = 2
        omega
      · -- r = 5
        omega