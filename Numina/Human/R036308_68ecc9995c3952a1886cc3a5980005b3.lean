import Mathlib

/-What is the smallest integer greater than 10 such that
the sum of the digits in its base 17 representation is equal to the sum of the digits in its base 10 representation?-/

theorem number_theory_608750: IsLeast {n: ℤ | 10 < n ∧ ∃ a b c d e f: ℤ, 0 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧
  0 ≤ c ∧ c ≤ 9 ∧ 0 ≤ d ∧ d ≤ 16 ∧ 0 ≤ e ∧ e ≤ 16 ∧ 0 ≤ f ∧ f ≤ 16 ∧
  n = 100 * a + 10 * b + c ∧ n = 289 * d + 17 * e + f ∧ a + b + c = d + e + f} 153:= by

  constructor

  -- the forward direction: show that 153 is in the set
  .
    simp only [Set.mem_setOf_eq]
    norm_num
    use 1
    norm_num
    use 5
    norm_num
    use 3
    norm_num
    use 0
    norm_num
    use 9
    norm_num


  -- the backward direction: show that if n is in the set, then 153 ≤ n
  .
    intro n h
    simp only [Set.mem_setOf_eq] at h
    rcases h with ⟨hn, h⟩
    obtain ⟨a, b, c, d, e, f, a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, f1, f2, h1, h2, h⟩ := h
    by_contra! l

    -- then we must have d = 0
    have ld: d = 0 := by omega
    simp [ld] at *
    clear d1 d2
    replace e2: e ≤ 8 := by omega
    replace a2: a ≤ 1 := by omega

    -- then a = 0 ∨ a = 1
    have ha: a = 0 ∨ a = 2 := by omega
    rcases ha with ha | ha

    -- case a = 0
    .
      simp [ha] at *
      replace b1: 1 ≤ b := by omega
      clear e2 a2 ha ld a1 l
      rw [h2] at h1
      have v: 9 * b = 16 * e := by omega
      have u: 16 ∣ 9 * b := by
        rw [v]
        simp
      replace u: 16 ∣ b := by
        apply IsCoprime.dvd_of_dvd_mul_left at u
        exact u
        norm_num

      -- then we must have b = 0
      have ob: b = 0 := by
        by_contra! o
        apply exists_eq_mul_right_of_dvd at u
        obtain ⟨k, hk⟩ := u
        have ok: 0 ≤ k := by omega
        have k1: k ≠ 0 := by omega
        replace ok: 1 ≤ k := by omega
        nlinarith
      simp [ob] at *

    -- case a = 1
    .
      simp [ha] at *