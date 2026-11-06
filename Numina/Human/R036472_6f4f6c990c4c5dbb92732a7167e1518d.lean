import Mathlib
/- Trouver tous les triplets d'entiers strictement positifs ( $a, b, c)$ tels que $6^{a}=1+2^{b}+$ $3^{\mathrm{c}}$. -/
theorem number_theory_607567 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ 6 ^ a = 1 + 2 ^ b + 3 ^ c} = {(1, 1, 1), (2, 3, 3), (2, 5, 1)}:= by
  -- Use extensionality to prove equality of sets
  ext ⟨a, b, c⟩
  constructor
  .
    -- Forward direction: if (a,b,c) satisfies the equation, then it's one of the three solutions
    intro h
    simp at h
    rcases h with ⟨h1, h2, h3, h4⟩
    -- Case analysis on whether b = 1
    by_cases h5 : b = 1
    .
      -- Case where b = 1
      subst b
      simp at h4
      -- Define A = a-1 and C = c-1 for cleaner calculations
      set A:= a - 1 with hA
      set C:= c - 1 with hC
      clear_value A C
      replace hA : a = A + 1:= by omega
      replace hC : c = C + 1:= by omega
      subst a c
      ring_nf at h4
      replace h4 : 2 * 6 ^ A = 1 + 3 ^ C:= by omega
      -- Subcase: A = 0
      by_cases h6 : A = 0
      .
        subst A
        simp at h4
        replace h4 : 3 ^ C = 1:= by omega
        -- If 3^C = 1, then C must be 0
        replace h4 : C = 0:= by
          by_contra H
          replace H : C ≥ 1:= by omega
          replace H : 3 ^ C ≥ 3 ^ 1:= by refine Nat.pow_le_pow_of_le_right (by omega) H
          linarith
        subst C
        simp
      .
        -- Subcase: A > 0
        -- Show that 3 divides 6^A and thus 2*6^A
        replace g1 : 3 ∣ 6 ^ A:= by
          have g2 : 3 ∣ 6:= by omega
          exact Dvd.dvd.pow g2 h6
        replace g1 : 3 ∣ 2 * 6 ^ A:= by exact (Nat.Coprime.dvd_mul_left (by decide)).mpr g1
        -- Check if C = 0
        by_cases h7 : C = 0
        .
          subst C
          simp at h4
          rw [h4] at g1
          simp at g1
          omega
        .
          -- If C > 0, derive a contradiction using divisibility by 3
          have g2 : 3 ∣ 3 ^ C:= by exact dvd_pow_self 3 h7
          rw [h4] at g1
          replace g1 : 3 ∣ 1:= by exact (Nat.dvd_add_iff_left g2).mpr g1
          omega
    .
      -- Case where b ≠ 1
      -- Prove that b must be odd
      have h6 : Odd b:= by
        by_contra H
        simp at H
        have h6 : 3 ∣ 1 + 2 ^ b:= by
          replace g1 : 3 ∣ 6 ^ a:= by
            have g2 : 3 ∣ 6:= by omega
            exact Dvd.dvd.pow g2 (by omega)
          have g2 : 3 ∣ 3 ^ c:= by exact dvd_pow_self 3 (by omega)
          rw [h4] at g1
          exact (Nat.dvd_add_iff_left g2).mpr g1
        -- Use modular arithmetic to derive a contradiction
        zify at h6
        replace h6 : 1 + 2 ^ b ≡ 0 [ZMOD 3]:= by exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int h6)
        have h7 : 2 ≡ -1 [ZMOD 3]:= by rfl
        replace h7 : 2 ^ b ≡ (-1) ^ b [ZMOD 3]:= by exact Int.ModEq.pow b h7
        rw [show (-1 : ℤ) ^ b = 1 by exact Even.neg_one_pow H] at h7
        replace h7 : 1 + 2 ^ b ≡ 1 + 1 [ZMOD 3]:= by exact Int.ModEq.add rfl h7
        replace h6 : 1 + 1 ≡ 0 [ZMOD 3]:= by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm h6)) h7)
        simp [Int.ModEq] at h6
      -- Since b is odd and not 1, b ≥ 3
      replace h5 : b ≥ 3:= by
        by_contra H
        replace H : b = 2:= by omega
        subst b
        absurd h6
        simp
      -- Prove that a ≥ 2 using size constraints
      have h7 : a ≥ 2:= by
        by_contra H
        simp at H
        replace H : a ≤ 1:= by omega
        replace H : 6 ^ a ≤ 6 ^ 1:= by refine Nat.pow_le_pow_of_le_right (by omega) H
        replace h5 : 2 ^ b ≥ 2 ^ 3:= by exact Nat.pow_le_pow_of_le_right (by omega) h5
        have g1 : 3 ^ c > 0:= by positivity
        linarith
      -- Prove that c must be odd using divisibility by 4
      have h8 : Odd c:= by
        have g2 : 4 ∣ 6 ^ a:= by
          set A:= a - 2 with hA
          clear_value A
          replace hA : a = A + 2:= by omega
          subst a
          ring_nf
          rw [show 6 ^ A * 36 = 9 * 6 ^ A * 4 by ring]
          simp
        have g3 : 4 ∣ 2 ^ b:= by
          set B:= b - 2 with hB
          clear_value B
          replace hB : b = B + 2:= by omega
          subst b
          ring_nf
          simp
        rw [h4] at g2
        rw [show 1 + 2 ^ b + 3 ^ c = 1 + 3 ^ c + 2 ^ b by ring] at g2
        replace g2 : 4 ∣ 1 + 3 ^ c:= by exact (Nat.dvd_add_iff_left g3).mpr g2
        -- Use modular arithmetic to prove c is odd
        by_contra H
        simp at H
        zify at g2
        replace g2 : 1 + 3 ^ c ≡ 0 [ZMOD 4]:= by exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int g2)
        have g4 : 3 ≡ -1 [ZMOD 4]:= by rfl
        replace g4 : 3 ^ c ≡ (-1) ^ c [ZMOD 4]:= by exact Int.ModEq.pow c g4
        rw [show (-1) ^ c = 1 by exact Even.neg_one_pow H] at g4
        replace g4 : 1 + 3 ^ c ≡ 1 + 1 [ZMOD 4]:= by exact Int.ModEq.add rfl g4
        replace g2 : 1 + 1 ≡ 0 [ZMOD 4]:= by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm g2)) g4)
        simp [Int.ModEq] at g2
      -- Prove that a = 2 using divisibility by 8
      have h9 : a = 2:= by
        have g1 : 8 ∣ 2 ^ b:= by
          set B:= b - 3 with hB
          clear_value B
          replace hB : b = B + 3:= by omega
          subst b
          ring_nf
          simp
        -- Show that 3^c ≡ 3 (mod 8) when c is odd
        have g2 : 3 ^ c ≡ 3 [ZMOD 8]:= by
          simp [Odd] at h8
          rcases h8 with ⟨k, hk⟩
          subst c
          ring_nf
          rw [show k * 2 = 2 * k by ring]
          rw [show (3 : ℤ) ^ (2 * k) = (3 ^ 2) ^ k by exact pow_mul 3 2 k]
          ring_nf
          have g2 : 9 ≡ 1 [ZMOD 8]:= by rfl
          replace g2 : 9 ^ k ≡ 1 ^ k [ZMOD 8]:= by exact Int.ModEq.pow k g2
          simp at g2
          replace g2 : 9 ^ k * 3 ≡ 1 * 3 [ZMOD 8]:= by exact Int.ModEq.mul g2 rfl
          simp at g2
          exact g2
        zify at g1
        replace g1 : 2 ^ b ≡ 0 [ZMOD 8]:= by exact Dvd.dvd.modEq_zero_int g1
        -- Prove a = 2 by contradiction
        by_contra H
        replace H : a ≥ 3:= by omega
        replace H : 8 ∣ 6 ^ a:= by
          set A:= a - 3 with hA
          clear_value A
          replace hA : a = A + 3:= by omega
          subst a
          ring_nf
          rw [show 6 ^ A * 216 = 6 ^ A * 27 * 8 by ring]
          simp
        zify at H h4
        replace H : 6 ^ a ≡ 0 [ZMOD 8]:= by exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int H)
        rw [h4] at H
        replace g1 : 1 + 2 ^ b ≡ 1 + 0 [ZMOD 8]:= by exact Int.ModEq.add rfl g1
        replace g2 : 1 + 2 ^ b + 3 ^ c ≡ 1 + 0 + 3 [ZMOD 8]:= by exact Int.ModEq.add g1 g2
        simp at g1 g2
        replace H : 4 ≡ 0 [ZMOD 8]:= by exact Int.ModEq.symm (Int.ModEq.trans (id (Int.ModEq.symm H)) g2)
        simp [Int.ModEq] at H
      -- Now we know a = 2, determine possible values for b
      subst a
      simp at h4
      replace h7 : b ≤ 5:= by
        by_contra H
        simp at H
        replace H : b ≥ 6:= by omega
        replace H : 2 ^ b ≥ 2 ^ 6:= by exact Nat.pow_le_pow_of_le_right h1 H
        have g1 : 3 ^ c > 0:= by positivity
        linarith
      -- Since b is odd and 3 ≤ b ≤ 5, b must be 3 or 5
      replace h7 : b = 3 ∨ b = 4 ∨ b = 5:= by omega
      rcases h7 with h7 | h7 | h7
      .
        -- Case b = 3
        subst b
        replace h4 : 3 ^ c = 3 ^ 3:= by omega
        replace h4 : Nat.log 3 (3 ^ c) = Nat.log 3 (3 ^ 3):= by rw [h4]
        rw [show Nat.log 3 (3 ^ c) = c by refine Nat.log_pow (by omega) c] at h4
        rw [show Nat.log 3 (3 ^ 3) = 3 by refine Nat.log_pow (by omega) 3] at h4
        subst c
        simp
      .
        -- Case b = 4 (impossible since b must be odd)
        subst b
        absurd h6
        simp
        decide
      .
        -- Case b = 5
        subst b
        replace h4 : 3 ^ c = 3 ^ 1:= by omega
        replace h4 : Nat.log 3 (3 ^ c) = Nat.log 3 (3 ^ 1):= by rw [h4]
        rw [show Nat.log 3 (3 ^ 1) = 1 by refine Nat.log_pow (by omega) 1] at h4
        rw [show Nat.log 3 (3 ^ c) = c by refine Nat.log_pow (by omega) c] at h4
        subst c
        simp
  .
    -- Backward direction: verify that each of the three claimed solutions satisfies the equation
    intro h
    simp at h
    rcases h with h | h | h
    all_goals
      rcases h with ⟨h1, h2, h3⟩
      subst a b c
      simp
