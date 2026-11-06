import Mathlib
set_option maxHeartbeats 400000
/- Let $K_0$ be a positive integer. Let $d_1$ and $d_2$ be digits (integers from 0 to 9 inclusive). Let $C$ be an integer that is divisible by 5 but not by 3 (for example, $C=1000$). Determine the number of pairs of digits $(d_1, d_2)$ such that the number $N = C \cdot (K_637390 + 10d_637390 + d_2)$ is divisible by 45. Show that if $K_0$ is divisible by 9 (i.e., $K_637390 \pmod 9 = 0$), the number of such pairs is 12, and otherwise, the number of such pairs is 11. -/
theorem algebra_637390 (c k : ℕ) (hc1 : 5 ∣ c) (hc2 : ¬3 ∣ c) : (k ≡ 0 [MOD 9] → {(d1, d2) : ℕ × ℕ | d1 ≤ 9 ∧ d2 ≤ 9 ∧ 45 ∣ c * (k + 10 * d1 + d2)}.ncard = 12) ∧ (¬k ≡ 0 [MOD 9] → {(d1, d2) : ℕ × ℕ | d1 ≤ 9 ∧ d2 ≤ 9 ∧ 45 ∣ c * (k + 10 * d1 + d2)}.ncard = 11):= by
  -- Split the proof into two cases using constructor
  constructor
  .
    -- Case 1: k ≡ 0 [MOD 9] (k is divisible by 9)
    intro h
    -- Define the set of valid pairs when k is divisible by 9
    have h1 : {(d1, d2) : ℕ × ℕ | d1 ≤ 9 ∧ d2 ≤ 9 ∧ 45 ∣ c * (k + 10 * d1 + d2)} = {(0, 0), (9, 9), (0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3), (7, 2), (8, 1), (9, 0)}:= by
      -- Prove set equality by showing both directions
      ext ⟨d1, d2⟩
      constructor
      .
        -- Forward direction: if (d1, d2) satisfies the conditions, then it's in our explicit set
        intro h1
        simp at h1
        rcases h1 with ⟨h1, h2, h3⟩
        -- Since 45 = 5 * 9 and c is divisible by 5, we need 9 to divide the remaining factor
        replace h3 : 9 ∣ c * (k + 10 * d1 + d2):= by omega
        -- Show that c is coprime with 3^2 = 9
        replace hc2 : Nat.Coprime 3 c:= by
          have h4 : Nat.Prime 3:= by norm_num
          exact (Nat.Prime.coprime_iff_not_dvd h4).mpr hc2
        replace hc2 : Nat.Coprime (3 ^ 2) c:= by exact Nat.Coprime.pow_left 2 hc2
        simp at hc2
        -- Since c is coprime with 9, 9 must divide k + 10 * d1 + d2
        replace h3 : 9 ∣ k + 10 * d1 + d2:= by exact Nat.Coprime.dvd_of_dvd_mul_left hc2 h3
        -- Since k is divisible by 9, k + 9 * d1 is also divisible by 9
        replace h : 9 ∣ k:= by exact Nat.dvd_of_mod_eq_zero h
        replace h : 9 ∣ k + 9 * d1:= by refine (Nat.dvd_add_iff_right h).mp (by simp)
        -- Rewrite the expression to isolate d1 + d2
        rw [show k + 10 * d1 + d2 = k + 9 * d1 + (d1 + d2) by ring] at h3
        -- Therefore 9 must divide d1 + d2
        replace h3 : 9 ∣ d1 + d2:= by omega
        rcases h3 with ⟨t, ht⟩
        -- Since 0 ≤ d1, d2 ≤ 9, the sum d1 + d2 can only be 0, 9, or 18
        have ht1 : t = 0 ∨ t = 2 ∨ t = 1:= by omega
        rcases ht1 with ht1 | ht1 | ht1
        .
          -- Case: d1 + d2 = 0, so d1 = d2 = 0
          subst t
          simp at ht
          rcases ht with ⟨rfl, rfl⟩
          simp
        .
          -- Case: d1 + d2 = 18, so d1 = d2 = 9
          subst t
          have g1 : d1 = 9:= by omega
          have g2 : d2 = 9:= by omega
          subst d1 d2
          simp
        .
          -- Case: d1 + d2 = 9, so d2 = 9 - d1
          subst t
          simp
          replace ht : d2 = 9 - d1:= by omega
          -- Check all possible values of d1 from 0 to 9
          have g : d1 = 0 ∨ d1 = 1 ∨ d1 = 2 ∨ d1 = 3 ∨ d1 = 4 ∨ d1 = 5 ∨ d1 = 6 ∨ d1 = 7 ∨ d1 = 8 ∨ d1 = 9:= by omega
          rcases g with g | g | g | g | g | g | g | g | g | g
          all_goals
            subst d1
            simp at ht
            subst d2
            simp
      .
        -- Backward direction: if (d1, d2) is in our explicit set, then it satisfies the conditions
        intro h1
        simp
        simp at h1
        -- Show that 45 divides c * (k + 10 * d1 + d2) by showing 9 divides k + 10 * d1 + d2
        rw [show 45 = 5 * 9 by omega]
        rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
        all_goals
          refine ⟨by omega, by omega, ?_⟩
          suffices 9 ∣ k + 10 * d1 + d2 by exact Nat.mul_dvd_mul hc1 this
          replace h : 9 ∣ k:= by exact Nat.dvd_of_mod_eq_zero h
          rw [show k + 10 * d1 + d2 = k + (10 * d1 + d2) by ring]
          suffices 9 ∣ 10 * d1 + d2 by exact Nat.dvd_add h this
          rcases h1 with ⟨rfl, rfl⟩
          omega
    -- Convert the set to a finset and count its elements
    rw [h1]
    rw [show ({(0, 0), (9, 9), (0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3), (7, 2), (8, 1), (9, 0)} : Set (ℕ × ℕ)) = ({(0, 0), (9, 9), (0, 9), (1, 8), (2, 7), (3, 6), (4, 5), (5, 4), (6, 3), (7, 2), (8, 1), (9, 0)} : Finset (ℕ × ℕ)) by simp]
    rw [Set.ncard_coe_Finset]
    -- Insert elements one by one and count
    repeat rw [Finset.card_insert_of_not_mem]
    any_goals
      simp
    tauto
  .
    -- Case 2: k ≢ 0 [MOD 9] (k is not divisible by 9)
    intro h
    -- Define the set of valid pairs when k is not divisible by 9
    have h1 : {(d1, d2) : ℕ × ℕ | d1 ≤ 9 ∧ d2 ≤ 9 ∧ 45 ∣ c * (k + 10 * d1 + d2)} = {(0, 9 - k % 9), (1, 9 - (k + 1) % 9), (2, 9 - (k + 2) % 9), (3, 9 - (k + 3) % 9), (4, 9 - (k + 4) % 9), (5, 9 - (k + 5) % 9), (6, 9 - (k + 6) % 9), (7, 9 - (k + 7) % 9), (8, 9 - (k + 8) % 9), (9, 9 - k % 9), (9 - k % 9, 0)}:= by
      -- Prove set equality by showing both directions
      ext ⟨d1, d2⟩
      constructor
      .
        -- Forward direction: if (d1, d2) satisfies the conditions, then it's in our explicit set
        intro h1
        simp at h1
        rcases h1 with ⟨h1, h2, h3⟩
        -- Since k is not divisible by 9, k % 9 ≠ 0
        replace h : k % 9 ≠ 0:= by
          by_contra H
          absurd h
          exact H
        -- Since 45 = 5 * 9 and c is divisible by 5, we need 9 to divide the remaining factor
        replace h3 : 9 ∣ c * (k + 10 * d1 + d2):= by omega
        -- Show that c is coprime with 3^2 = 9
        replace hc2 : Nat.Coprime 3 c:= by
          have h4 : Nat.Prime 3:= by norm_num
          exact (Nat.Prime.coprime_iff_not_dvd h4).mpr hc2
        replace hc2 : Nat.Coprime (3 ^ 2) c:= by exact Nat.Coprime.pow_left 2 hc2
        simp at hc2
        -- Since c is coprime with 9, 9 must divide k + 10 * d1 + d2
        replace h3 : 9 ∣ k + 10 * d1 + d2:= by exact Nat.Coprime.dvd_of_dvd_mul_left hc2 h3
        -- Rewrite the expression to isolate k + d1 + d2
        rw [show k + 10 * d1 + d2 = k + d1 + d2 + 9 * d1 by ring] at h3
        -- Since 9 divides 9 * d1, 9 must also divide k + d1 + d2
        replace h3 : 9 ∣ k + d1 + d2:= by
          have g : 9 ∣ 9 * d1:= by simp
          exact (Nat.dvd_add_iff_left g).mpr h3
        -- Consider two cases: d2 = 0 or d2 ≠ 0
        by_cases h4 : d2 = 0
        .
          -- Case: d2 = 0
          subst d2
          simp at h3
          -- Show that k + d1 ≡ 0 [MOD 9]
          replace h3 : k + d1 ≡ 0 [MOD 9]:= by exact Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat h3)
          -- Add 9 - d1 to both sides
          replace h3 : 9 - d1 + (k + d1) ≡ 9 - d1 + 0 [MOD 9]:= by exact Nat.ModEq.add_left (9 - d1) h3
          rw [show 9 - d1 + (k + d1) = 9 + k by omega] at h3
          simp at h3
          -- Simplify 9 + k ≡ k [MOD 9]
          replace h4 : 9 + k ≡ 0 + k [MOD 9]:= by simp
          rw [show 0 + k = k by omega] at h4
          -- Conclude that 9 - d1 ≡ k [MOD 9]
          replace h3 : 9 - d1 ≡ k [MOD 9]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm h3)) h4
          -- Show that (9 - d1) % 9 = 9 - d1
          have h5 : (9 - d1) % 9 = 9 - d1:= by
            have g : 9 - d1 < 9:= by
              by_contra H
              replace H : d1 = 0:= by omega
              subst d1
              simp at h3
              absurd h
              rw [←h3]
            exact Nat.mod_eq_of_lt g
          -- Conclude that d1 = 9 - k % 9
          replace h3 : (9 - d1) % 9 = k % 9:= by exact h3
          rw [h5] at h3
          replace h3 : d1 = 9 - k % 9:= by omega
          subst d1
          simp
        .
          -- Case: d2 ≠ 0
          -- Show that k + d1 + d2 ≡ 0 [MOD 9]
          replace h3 : k + d1 + d2 ≡ 0 [MOD 9]:= by exact Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat h3)
          -- Add 9 - d2 to both sides
          replace h3 : 9 - d2 + (k + d1 + d2) ≡ 9 - d2 + 0 [MOD 9]:= by exact Nat.ModEq.add_left (9 - d2) h3
          simp at h3
          rw [show 9 - d2 + (k + d1 + d2) = 9 + k + d1 by omega] at h3
          -- Simplify 9 + k + d1 ≡ k + d1 [MOD 9]
          have h5 : 9 + k + d1 ≡ k + d1 [MOD 9]:= by
            rw [show 9 + k + d1 = 9 + (k + d1) by ring]
            simp
          -- Conclude that 9 - d2 ≡ k + d1 [MOD 9]
          replace h5 : 9 - d2 ≡ k + d1 [MOD 9]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm h3)) h5
          -- Show that (9 - d2) % 9 = 9 - d2
          have h6 : (9 - d2) % 9 = 9 - d2:= by
            have g : 9 - d2 < 9:= by omega
            exact Nat.mod_eq_of_lt g
          -- Conclude that d2 = 9 - (k + d1) % 9
          replace h5 : (9 - d2) % 9 = (k + d1) % 9:= by exact h5
          rw [h6] at h5
          replace h5 : d2 = 9 - (k + d1) % 9:= by omega
          -- Check all possible values of d1 from 0 to 9
          replace h1 : d1 = 0 ∨ d1 = 1 ∨ d1 = 2 ∨ d1 = 3 ∨ d1 = 4 ∨ d1 = 5 ∨ d1 = 6 ∨ d1 = 7 ∨ d1 = 8 ∨ d1 = 9:= by omega
          rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
          all_goals
            subst d1
            simp at h5
            subst d2
            simp
      .
        -- Backward direction: if (d1, d2) is in our explicit set, then it satisfies the conditions
        intro h1
        simp at h1
        simp
        refine ⟨by omega, by omega, ?_⟩
        -- Show that 45 divides c * (k + 10 * d1 + d2) by showing 9 divides k + 10 * d1 + d2
        rw [show 45 = 5 * 9 by omega]
        suffices 9 ∣ k + 10 * d1 + d2 by exact Nat.mul_dvd_mul hc1 this
        rw [show k + 10 * d1 + d2 = k + d1 + d2 + 9 * d1 by ring]
        have g : 9 ∣ 9 * d1:= by simp
        suffices 9 ∣ k + d1 + d2 by exact (Nat.dvd_add_iff_right this).mp g
        rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
        all_goals
          rcases h1 with ⟨rfl, rfl⟩
          omega
    -- Convert the set to a finset and count its elements
    rw [h1]
    rw [show ({(0, 9 - k % 9), (1, 9 - (k + 1) % 9), (2, 9 - (k + 2) % 9), (3, 9 - (k + 3) % 9), (4, 9 - (k + 4) % 9), (5, 9 - (k + 5) % 9), (6, 9 - (k + 6) % 9), (7, 9 - (k + 7) % 9), (8, 9 - (k + 8) % 9), (9, 9 - k % 9), (9 - k % 9, 0)} : Set (ℕ × ℕ)) = ({(0, 9 - k % 9), (1, 9 - (k + 1) % 9), (2, 9 - (k + 2) % 9), (3, 9 - (k + 3) % 9), (4, 9 - (k + 4) % 9), (5, 9 - (k + 5) % 9), (6, 9 - (k + 6) % 9), (7, 9 - (k + 7) % 9), (8, 9 - (k + 8) % 9), (9, 9 - k % 9), (9 - k % 9, 0)} : Finset (ℕ × ℕ)) by simp]
    rw [Set.ncard_coe_Finset]
    -- Insert elements one by one and count
    repeat rw [Finset.card_insert_of_not_mem]
    any_goals
      simp
    all_goals
      intro h
      omega
