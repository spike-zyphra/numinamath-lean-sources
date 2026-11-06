import Mathlib

/- Given four different non-zero digits, it is possible to form 24 different four-digit numbers containing each of these four digits.
What is the largest prime factor of the sum of the 24 numbers?
A 23
B 93
C 97
D 101
E 113
 -/

theorem number_theory_242562 (a b c d : ℕ) (h1: 0 < a) (h2: a < b) (h3: b < c) (h4: c < d) (h5: d < 10):
    IsGreatest {p | Nat.Prime p ∧
    p ∣ (1000*a + 100*b + 10*c + d) +
      (1000*a + 100*b + 10*d + c) +
      (1000*a + 100*c + 10*b + d) +
      (1000*a + 100*c + 10*d + b) +
      (1000*a + 100*d + 10*b + c) +
      (1000*a + 100*d + 10*c + b) +
      (1000*b + 100*a + 10*c + d) +
      (1000*b + 100*a + 10*d + c) +
      (1000*b + 100*c + 10*a + d) +
      (1000*b + 100*c + 10*d + a) +
      (1000*b + 100*d + 10*a + c) +
      (1000*b + 100*d + 10*c + a) +
      (1000*c + 100*a + 10*b + d) +
      (1000*c + 100*a + 10*d + b) +
      (1000*c + 100*b + 10*a + d) +
      (1000*c + 100*b + 10*d + a) +
      (1000*c + 100*d + 10*a + b) +
      (1000*c + 100*d + 10*b + a) +
      (1000*d + 100*a + 10*b + c) +
      (1000*d + 100*a + 10*c + b) +
      (1000*d + 100*b + 10*a + c) +
      (1000*d + 100*b + 10*c + a) +
      (1000*d + 100*c + 10*a + b) +
      (1000*d + 100*c + 10*b + a)} 101 := by

    constructor

    -- the foward direction
    .
      simp
      refine ⟨(by norm_num), ?_⟩
      ring_nf
      rw [show a * 6666 + b * 6666 + c * 6666 + d * 6666 = 101 * (66 * (a + b + c + d)) by ring]
      simp

    -- the backward direction
    .
      intro p
      simp
      intro hp h
      ring_nf at h
      by_contra! l
      have o: Nat.Coprime p 6666 := by
        clear *- l hp
        rw [show 6666 = 101 * 66 by norm_num]
        apply Nat.Coprime.mul_right
        all_goals rw [Nat.Prime.coprime_iff_not_dvd]
        .
          by_contra! g
          apply Nat.le_of_dvd at g
          omega
          norm_num
        .
          tauto
        .
          by_contra! g
          apply Nat.le_of_dvd at g
          omega
          norm_num
        .
          tauto

      rw [show a * 6666 + b * 6666 + c * 6666 + d * 6666 = 6666 * (a + b + c + d) by ring] at h
      apply Nat.Coprime.dvd_of_dvd_mul_left o at h
      apply Nat.le_of_dvd at h
      omega
      omega
