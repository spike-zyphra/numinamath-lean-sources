import Mathlib

/-Show that the only five-digit natural number $n$ such that $n$ is 9 times its reversal is $98901$.
A number's reversal is obtained by writing its decimal digits in reverse order. For example, the reversal of $12345$ is $54321$.
We are looking for a five-digit number $n = abcde$ (where $a,b,c,d,e$ are its digits and $a \neq 0$) such that $n = 9 \times edcba$.-/

theorem number_theory_638440: {n: ℤ | ∃ a b c d e, 1 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧ 0 ≤ c ∧ c ≤ 9 ∧
  0 ≤ d ∧ d ≤ 9 ∧ 0 < e ∧ e ≤ 9 ∧ n = a * 10000 + b * 1000 + c * 100 + d * 10 + e ∧
  n = 9 * (e * 10000 + d * 1000 + c * 100 + b * 10 + a)} = {98901} := by

  ext n
  constructor

  -- the forward direction
  .
    simp only [Set.mem_setOf_eq]
    intro h
    simp
    obtain ⟨a, b, c, d, e, la, ra, lb, rb, lc, rc, ld, rd, le, re, hn, h⟩ := h
    rw [hn] at h

    -- we show that a must be 9
    have va: a = 9 := by
      clear hn
      nlinarith

    simp [va] at *

    -- we show e must be 1
    have ve: e = 1 := by
      clear hn
      omega

    simp [ve] at *

    replace h: 100 * b + 10 * c + d = 9000 * d + 90 * c + 9 * b + 8 := by
      omega

    -- then d must be 0
    have vd: d = 0 := by
      clear hn
      omega

    simp [vd] at *

    replace h: 91 * b = 80 * c + 8 := by
      clear hn
      omega

    -- then b must be 8
    have vb: b = 8 := by
      clear hn
      have db: 8 ∣ b := by
        suffices 8 ∣ 91 * b by
          exact IsCoprime.dvd_of_dvd_mul_left (by norm_num) this
        rw [h]
        rw [show 80 * c + 8 = 8 * (10 * c + 1) by omega]
        simp
      apply exists_eq_mul_right_of_dvd at db
      obtain ⟨k, hk⟩ := db
      have lk: k ≤ 1 := by omega
      have rk: k ≥ 0 := by omega
      interval_cases k
      .
        simp at hk
        simp [hk] at h
        omega
      .
        simp at hk
        tauto

    simp [vb] at *
    replace h: c = 9 := by omega
    simp [h] at *
    tauto


  -- the backward direction
  .
    intro h
    simp at h
    simp only [Set.mem_setOf_eq, h]
    use 9, 8, 9, 0, 1
    norm_num