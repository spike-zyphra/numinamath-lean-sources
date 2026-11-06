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


theorem number_theory_184446: IsLeast {n: ℕ | ∃ a b c, 0 < a ∧ 0 < b ∧ 0 < c ∧
  a ^ b % 10 = 4 ∧ b ^ c % 10 = 2 ∧ c ^ a % 10 = 9 ∧ n = a + b + c} 17 := by
  constructor
  · -- Show 17 is in the set
    use 2, 2, 13
    all_goals norm_num
  · -- Show it is minimal
    intro n hn
    rcases hn with ⟨a, b, c, ha, hb, hc, h1, h2, h3, hn⟩
    by_contra h
    push_neg at h
    have h4 : a ≤ 14 := by
      omega
    have h5 : b ≤ 14 := by
      omega
    have h6 : c ≤ 14 := by
      omega
    interval_cases a <;> interval_cases b <;> interval_cases c
    <;> norm_num at h1 h2 h3 hn
    <;> omega