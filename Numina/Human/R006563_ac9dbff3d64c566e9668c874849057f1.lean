import Mathlib

/-Let $k_0$ be a positive integer. Mary has four children of different positive ages.
All ages are less than or equal to $k_0+3$. The product of their ages is $P_0 = k_0(k_0+1)(k_0+2)(k_0+3)$.
If $k_0=7$ (so all ages are $\le 10$ and the product is $7 \cdot 8 \cdot 9 \cdot 10 = 5040$),
determine the sum of the ages of Mary's children. Show the answer is $4k_0+6 = 34$.-/

theorem number_theory_638495 (a b c d: ℕ) (l1: a < b) (l2: b < c) (l3: c < d) (l4: d ≤ 10) (h: a * b * c * d = 5040):
  a + b + c + d = 34 := by

    -- we show that d is at least 10
    have ld: 9 < d := by
      by_contra! l
      have s1: a ≤ 6 := by
        omega
      have s2: b ≤ 7 := by
        omega
      have s3: c ≤ 8 := by
        omega
      have s4: a * b ≤ 42 := by
        nlinarith
      have s5: a * b * c ≤ 336 := by
        nlinarith
      have s6: a * b * c * d ≤ 336 * 9 := by
        nlinarith
      simp [h] at s6

    -- hence d must be 10
    have vd: d = 10 := by omega
    simp [vd] at *
    replace h: a * b * c = 504 := by omega

    -- similarly, we derive 8 < c
    have lc: 8 < c := by
      by_contra! l
      have s1: a ≤ 6 := by
        omega
      have s2: b ≤ 7 := by
        omega
      have s3: c ≤ 8 := by
        omega
      have s4: a * b ≤ 42 := by
        nlinarith
      have s5: a * b * c ≤ 336 := by
        nlinarith
      simp [h] at s5

    -- then c = 9
    have vc: c = 9 := by omega
    simp [vc] at *
    replace h: a * b = 56 := by omega

    -- similarly 7 < b
    have lb: 7 < b := by
      by_contra! l
      have s1: a ≤ 6 := by
        omega
      have s3: a * b ≤ 42 := by
        nlinarith
      simp [h] at s3

    -- hence b = 8
    have vb: b = 8 := by omega
    simp [vb] at *
    omega