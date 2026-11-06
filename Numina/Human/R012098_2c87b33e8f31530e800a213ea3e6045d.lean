import Mathlib

lemma lemma_1 {a b c: ℕ} (h: b ∣ c): a % c % b = a % b := by
  zify
  rw [Int.emod_emod_of_dvd]
  zify at h
  exact h

lemma lemma_2 {c a: ℕ} (ha: Even a) (h: c ^ a % 10 = 9): c % 10 = 3 ∨ c % 10 = 7 := by
  rw [Nat.pow_mod] at h
  set x:= c % 10
  have lx: x < 10 := by omega
  clear_value x
  have ox: Odd x := by
    by_contra! o
    simp at o
    replace o: Even (x ^ a) := by
      rw [Nat.even_pow']
      exact o
      by_contra! s
      simp [s] at h
    apply Even.two_dvd at o
    have u: 2 ∣ 10 := by norm_num
    rw [← Nat.dvd_mod_iff u] at o
    rw [h] at o
    norm_num at o
  by_contra! ne
  have v: x = 1 ∨ x = 5 ∨ x = 9 := by
    by_contra! l
    interval_cases x
    all_goals absurd ox; norm_num; try decide
    all_goals try omega
  have la: 0 < a := by
      by_contra! o
      replace o: a = 0 := by omega
      simp [o] at h
  rcases v with v | v | v
  -- case 1: x = 1
  .
    simp [v] at h

  -- case 2: x = 5
  .
    simp [v] at h
    clear * - h ha la
    have o: 5 ∣ 5 ^ a % 10 := by
      rw [Nat.dvd_mod_iff]
      rw [show a = a - 1 + 1 by omega]
      rw [Nat.pow_add]
      rw [show 5 ^ 1 = 5 by norm_num]
      simp
      norm_num
    rw [h] at o
    norm_num at o

  -- case 3: x = 9
  .
    simp [v] at h
    clear * - h ha la
    rw [even_iff_exists_two_mul] at ha
    obtain ⟨k, s⟩ := ha
    rw [s] at h
    rw [show 9 ^ (2 * k) = (9 ^ 2) ^ k by apply Nat.pow_mul] at h
    norm_num at h
    rw [Nat.pow_mod] at h
    rw [show 81 % 10 = 1 by norm_num] at h
    rw [show 1 ^ k = 1 by norm_num] at h
    norm_num at h


/-Positive integers a,b, and c have the property that
a^b,b^c,c^a end in 4,2 , and 9 , respectively.
Compute the minimum possible value of a+b+c.-/

theorem number_theory_184446: IsLeast {n: ℕ | ∃ a b c, 0 < a ∧ 0 < b ∧ 0 < c ∧
  a ^ b % 10 = 4 ∧ b ^ c % 10 = 2 ∧ c ^ a % 10 = 9 ∧ n = a + b + c} 17 := by

  constructor

  -- the forward direction
  .
    simp
    use 2
    norm_num
    use 2
    norm_num
    use 13
    norm_num

  -- the backward direction
  .
    intro n h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨a, b, c, l1, l2, l3, d1, d2, d3, hn⟩ := h
    rw [hn]
    clear hn

    -- for convenience, we prove by contradiction
    by_contra! l

    -- we show a and b are both even
    have oa: Even a := by
      replace d1: a ^ b % 10 % 2 = 0 := by
        rw [d1]
      rw [lemma_1] at d1
      apply Nat.dvd_of_mod_eq_zero at d1
      rw [← even_iff_two_dvd] at d1
      rw [Nat.even_pow'] at d1
      exact d1
      omega
      norm_num
    have ob: Even b := by
      replace d2: b ^ c % 10 % 2 = 0 := by
        rw [d2]
      rw [lemma_1] at d2
      apply Nat.dvd_of_mod_eq_zero at d2
      rw [← even_iff_two_dvd] at d2
      rw [Nat.even_pow'] at d2
      exact d2
      omega
      norm_num

    have fa:= oa
    rw [even_iff_exists_two_mul] at oa ob
    obtain ⟨x, hx⟩ := oa
    obtain ⟨y, hy⟩ := ob
    simp [hx, hy] at l l1 l2 l3

    -- then c < 13
    have lc: c < 13 := by
      by_contra! o
      nlinarith

    -- use lemma 2 to get c
    have i:= lemma_2 fa d3
    replace i: c = 3 ∨ c = 7 := by omega
    rcases i with i | i

    -- case 1: c = 3
    .
      simp [i] at *
      replace l: x + y < 7 := by omega
      simp [hx, hy] at *
      have lx: x < 6 := by omega
      have ly: y < 6 := by omega
      interval_cases x
      all_goals norm_num at d3 d1
      .
        interval_cases y
        all_goals norm_num at d1 d2
      .
        replace l: y < 4 := by omega
        interval_cases y
        all_goals norm_num at d1 d2
      .
        replace l: y < 2 := by omega
        have o: y = 1 := by omega
        simp [o] at d2

    -- case 2: c = 7
    .
      simp [i] at *
      replace l: x + y < 5 := by omega
      simp [hx, hy] at *
      have lx: x < 4 := by omega
      have ly: y < 4 := by omega
      interval_cases x
      all_goals norm_num at d3 d1
      .
        interval_cases y
        all_goals norm_num at d1 d2
      .
        replace l: y < 2 := by omega
        have o: y = 1 := by omega
        simp [o] at d2
        
