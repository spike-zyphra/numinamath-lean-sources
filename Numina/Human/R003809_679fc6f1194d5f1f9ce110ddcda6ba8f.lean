import Mathlib

-- we show all possble cases for n^2 % 8 and n^2 % 4
lemma sq_mod_8 (n: ℕ): n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4:= by
  rw [Nat.pow_mod]
  set x := n % 8
  have l: 0 ≤ x := by omega
  have r: x < 8 := by omega
  clear_value x
  interval_cases x
  all_goals omega

lemma sq_mod_4 (n: ℕ): n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  rw [Nat.pow_mod]
  set x:= n % 4
  have l: 0 ≤ x := by omega
  have r: x < 4 := by omega
  clear_value x
  interval_cases x
  all_goals omega

-- we first prove for the case a ≤ b ≤ c, then we can use the symmetry of the problem
lemma lemma_1 {a b c n: ℕ} (l0: 0 < a) (l1: a ≤ b) (l2: b ≤ c) (h: 2 ^ a + 2 ^ b + 2 ^ c + 3 = n ^ 2) :
  a = 1 ∧ b = 1 ∧ c = 1 ∨ a = 1 ∧ b = 2 ∧ c = 4 := by

    -- for convenience, we prove by contradiction
    by_contra! ne

    -- we show that a = 1 firstly
    have va: a = 1 := by
      suffices a < 2 by omega
      by_contra! f
      replace h: (2 ^ a + 2 ^ b + 2 ^ c + 3) % 4 = n ^ 2 % 4:= by
        rw [h]
      rw [Nat.add_mod] at h
      have j: (2 ^ a + 2 ^ b + 2 ^ c) % 4 = 0 := by
        rw [Nat.add_mod]
        have f1: 2 ^ c % 4 = 0 := by
          apply Nat.mod_eq_zero_of_dvd
          rw [show c = c - 2 + 2 by omega]
          ring_nf
          simp
        simp [f1]
        rw [Nat.add_mod]
        have f2: 2 ^ b % 4 = 0 := by
          apply Nat.mod_eq_zero_of_dvd
          rw [show b = b - 2 + 2 by omega]
          ring_nf
          simp
        simp [f2]
        have f3: 2 ^ a % 4 = 0 := by
          apply Nat.mod_eq_zero_of_dvd
          rw [show a = a - 2 + 2 by omega]
          ring_nf
          simp
        simp [f3]
      simp [j] at h
      have i:= sq_mod_4 n
      omega

    simp [va] at *

    -- then we show that b ≤ 2 by mod 8
    have lb: b < 3 := by
      by_contra! f
      ring_nf at h
      replace h: (5 + 2 ^ b + 2 ^ c) % 8 = n ^ 2 % 8 := by
        rw [h]
      rw [Nat.add_mod] at h
      have f1: 2 ^ c % 8 = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        rw [show c = c - 3 + 3 by omega]
        ring_nf
        simp
      simp [f1] at h
      rw [Nat.add_mod] at h
      have f2: 2 ^ b % 8 = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        rw [show b = b - 3 + 3 by omega]
        ring_nf
        simp
      simp [f2] at h
      have i := sq_mod_8 n
      omega

    -- then we check b = 1 and b = 2 separately
    have vb: b = 1 ∨ b = 2 := by omega
    rcases vb with vb | vb

    -- case b = 1
    .
      simp [vb] at *
      ring_nf at h
      have lc: c < 3 := by
        by_contra! f
        replace h: (7 + 2 ^ c) % 4 = n ^ 2 % 4 := by
          rw [h]
        rw [Nat.add_mod] at h
        have s: 2 ^ c % 4 = 0 := by
          apply Nat.mod_eq_zero_of_dvd
          rw [show c = c - 2 + 2 by omega]
          ring_nf
          simp
        simp [s] at h
        have i:= sq_mod_4 n
        omega
      interval_cases c
      -- case c = 1
      .
        norm_num at ne
      -- case c = 2
      .
        simp at h
        have o: IsSquare 11 := by
          rw [h]
          apply IsSquare.sq
        absurd o
        native_decide

    -- case b = 2
    .
      simp [vb] at *
      ring_nf at h
      have rn: 3 ^ 2 ≤ n ^ 2 := by
        simp
        rw [← h]
        simp
      have ln: 3 ≤ n := by
        suffices 3 ^ 2 ≤ n ^ 2 by
          rw [Nat.pow_le_pow_iff_left] at this
          exact this
          norm_num
        exact rn
      simp at rn
      replace h: 2 ^ c = n ^ 2 - 9 := by omega
      have eq: n ^ 2 - 9 = (n - 3) * (n + 3) := by
        zify
        have u1: ↑(n ^ 2 - (9: ℕ)) = ↑n ^ 2 - (9: ℤ) := by
          apply Int.natCast_sub
          tauto
        have u2: ↑(n - (3: ℕ)) = ↑n - (3: ℤ) := by
          apply Int.natCast_sub
          tauto
        simp [u1, u2]
        ring
      rw [eq] at h
      clear eq
      have v1: n - 3 ∣ 2 ^ c := by
        rw [h]
        simp
      rw [Nat.dvd_prime_pow] at v1
      obtain ⟨c1, v1⟩ := v1
      rcases v1 with ⟨u1, v1⟩
      have v2: n + 3 ∣ 2 ^ c := by
        rw [h]
        simp
      rw [Nat.dvd_prime_pow] at v2
      obtain ⟨c2, v2⟩ := v2
      rcases v2 with ⟨u2, v2⟩
      have v3: c1 + c2 = c := by
        simp [v1, v2] at h
        rw [show 2 ^ c1 * 2 ^ c2 = 2 ^ (c1 + c2) by ring] at h
        rw [pow_right_inj₀] at h
        simp [h]
        norm_num
        norm_num
      clear h u1 u2
      have k: 2 ^ c1 + 6 = 2 ^ c2 := by
        simp [← v1, ← v2]
        omega
      have s: c1 ≤ c2 := by
        suffices 2 ^ c1 ≤ 2 ^ c2 by
          rw [Nat.pow_le_pow_iff_right] at this
          exact this
          norm_num
        rw [← v1, ← v2]
        omega

      -- then we show that c1 < 2 by mod 4
      have i: c1 < 2 := by
        by_contra! i
        replace k: (2 ^ c1 + 6) % 4 = 2 ^ c2 % 4 := by
          rw [k]
        rw [Nat.add_mod] at k
        have f1: 2 ^ c1 % 4 = 0 := by
          apply Nat.mod_eq_zero_of_dvd
          rw [show c1 = c1 - 2 + 2 by omega]
          ring_nf
          simp
        simp [f1] at k
        have f2: 2 ^ c2 % 4 = 0 := by
          apply Nat.mod_eq_zero_of_dvd
          rw [show c2 = c2 - 2 + 2 by omega]
          ring_nf
          simp
        simp [f2] at k

      interval_cases c1
      .
        simp at k
        have o: 2 ∣ 7 := by
          rw [k]
          rw [show c2 = c2 - 1 + 1 by omega]
          ring_nf
          simp
        norm_num at o
      .
        simp at k
        rw [show 8 = 2 ^ 3 by norm_num] at k
        rw [pow_right_inj₀] at k
        simp [← k] at v3
        simp [v3] at ne
        norm_num
        norm_num

      norm_num
      norm_num


/-Determine all ordered triples of positive numbers
(a,b,c) for which 2^a+2^b+2^c+3
is a square of some natural number.-/

theorem number_theory_213315: {(a, b, c): ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ∃ n, 2 ^ a + 2 ^ b + 2 ^ c + 3 = n ^ 2}
  = {(1, 1, 1), (1, 2, 4), (1, 4, 2), (2, 1, 4), (2, 4, 1), (4, 1, 2), (4, 2, 1)} := by

    ext ⟨a, b, c⟩
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      rcases h with ⟨ha, hb, hc, h⟩
      obtain ⟨n, h⟩ := h
      simp
      have u: (a ≤ b ∧ b ≤ c) ∨ (a ≤ c ∧ c ≤ b) ∨ (b ≤ a ∧ a ≤ c) ∨
        (b ≤ c ∧ c ≤ a) ∨ (c ≤ a ∧ a ≤ b) ∨ (c ≤ b ∧ b ≤ a) := by omega

      -- By symmetry lemma_1 can be used on for all cases of ordered triples of $a,b,c$
      rcases u with u | u | u | u | u | u 
      <;> rcases u with ⟨u, v⟩
      <;> rcases (lemma_1 (by omega) u v (by linarith)) with i | i
      <;> all_goals simp [i]
    

    -- The backward direction, we show that all triples satisfy the equation
    .
      intro h
      simp at h
      rcases h with h | h | h | h | h | h | h
      all_goals simp [h]
      
      · use 3; norm_num

      all_goals use 5; norm_num

 