import Mathlib

/-Find all four-digit numbers A that satisfy the following three conditions:
a) the first digit of A is twice as small as the last;
b) the second and third digits of A are the same;
c) if the number A is decreased by 2, the result is divisible by 143.
-/

theorem number_theory_242382: {A: ℤ | 143 ∣ A - 2 ∧ ∃ a b d: ℤ, 1 ≤ a ∧ a < 10 ∧ 0 ≤ b ∧ b < 10
∧ d < 10 ∧ d = 2 * a ∧ A = 1000 * a + 100 * b + 10 * b + d} = {2004} := by

 ext A
 constructor

 -- the forward direction
 .
  intro h
  simp only [Set.mem_setOf_eq] at h
  rcases h with ⟨h0, h⟩
  obtain ⟨a, b, d, la, ra, lb, rb, rd, h1, h2⟩ := h
  simp
  rw [h1] at h2
  rw [show 1000 * a + 100 * b + 10 * b + 2 * a = 1002 * a + 110 * b by ring] at h2
  have d1: 11 ∣ A - 2 := by
    have o: 11 ∣ 143 := by
      norm_num
    zify at o
    apply dvd_trans o h0
  rw [h2] at d1
  rw [show 1002 * a + 110 * b - 2 = 11 * (91 * a + 10 * b) + a - 2 by ring] at d1

  -- then we have a = 2
  replace d1: 11 ∣ a - 2 := by
    rw [show a - 2 = 11 * (91 * a + 10 * b) + a - 2 - (11 * (91 * a + 10 * b)) by ring]
    apply dvd_sub
    exact d1
    simp
  apply exists_eq_mul_right_of_dvd at d1
  obtain ⟨k, hk⟩ := d1
  have lk: k < 1 := by
    nlinarith
  have uk: 0 ≤ k := by
    nlinarith
  have ok: k = 0 := by omega
  clear lk uk
  simp [ok] at hk
  replace hk: a = 2 := by omega
  simp [hk] at h2
  simp [h2] at h0
  ring_nf at h0

  -- then we show that b = 0
  replace h0: 13 ∣ 2002 + b * 110 := by
    have o: 13 ∣ 143 := by
      norm_num
    zify at o
    apply dvd_trans o h0
  replace h0: 13 ∣ b * 110 := by
    rw [show b * 110 = 2002 + b * 110 - 2002 by ring]
    apply dvd_sub
    exact h0
    norm_num
  -- note that 13 and 110 are coprime
  apply IsCoprime.dvd_of_dvd_mul_right  at h0
  .
    apply exists_eq_mul_right_of_dvd at h0
    obtain ⟨s, hs⟩ := h0
    have ls: s < 1 := by
      nlinarith
    have us: 0 ≤ s := by
      nlinarith
    have os: s = 0 := by omega
    simp [os] at hs
    simp [hs] at h2
    exact h2
  .
    norm_num


-- the backward direction
 .
  intro h
  simp at h
  simp [h]
  norm_num
  use 2
  norm_num
  use 0
  norm_num
  use 4
  norm_num