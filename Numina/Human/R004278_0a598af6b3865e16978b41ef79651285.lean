import Mathlib

lemma lemma_1 (a: ℤ) (ha: 0 < a): 1312 - a * 850 + a ^ 2 * 111 ≠ 0 := by
  by_contra! h
  have ra: a < 6 := by nlinarith
  have la: 2 < a := by nlinarith
  interval_cases a
  .
    simp at h
  .
    simp at h
  .
    simp at h

/-Given x=-2272,y=10^3+10^2c+10b+a, z=1 satisfies the equation
ax+by+cz=1, where a,b,c are positive integers, a < b < c. Find y-/

theorem algebra_247618 {x y z a b c: ℤ} (hx: x = -2272) (hy: y = 10^3 + 10^2 * c + 10*b + a) (hz: z = 1)
    (l1: 0 < a) (l2: a < b) (l3: b < c) (h: a*x + b*y + c*z = 1) : y = 1987 := by

  simp [hx, hz, hy] at h
  simp [hy]
  clear hy
  clear hx hz
  replace h: b * (1000 + 100 * c + 10 * b + a) + c - 2272 * a - 1 = 0 := by linarith

  -- then we show that b < a + 2
  have lb: b < a + 2 := by
    by_contra! l
    have l4: a + 3 ≤ c := by omega
    replace h: (a + 2) * (1000 + 100 * (a + 3) + 10 * (a + 2) + a) + (a + 3) - 2272 * a - 1 ≤ 0 := by
      nlinarith
    ring_nf at h
    nlinarith

  -- hence b = a + 1 indeed
  have vb: b = a + 1 := by omega
  simp [vb] at *

  -- then we show that c < a + 4
  have lc: c < a + 4 := by
    by_contra! l
    replace h: (a + 1) * (1000 + 100 * (a + 4) + 10 * (a + 1) + a) + (a + 4) - 2272 * a - 1 ≤ 0 := by
      nlinarith
    ring_nf at h
    absurd h
    simp
    rify
    rw [show (1413: ℝ) - a * 750 + a ^ 2 * 111 = 111 * (a - 375 / 111) ^ 2 + 1413 - 375 ^ 2 / 111 by ring]
    nlinarith

  -- hence c = a + 3 ∨ c = a + 2
  have vc: c = a + 3 ∨ c = a + 2 := by omega
  rcases vc with t | t

  -- case c = a + 3
  .
    simp [t] at h
    ring_nf at h
    absurd h
    apply lemma_1
    exact l1

  -- case c = a + 2
  .
    simp [t] at h
    ring_nf at h
    rw [show 1211 - a * 950 + a ^ 2 * 111 = (a - 7) * (111 * a - 173) by ring] at h
    simp at h
    rcases h with h | h
    .
      replace h: a = 7 := by linarith
      simp [h] at t
      simp [h, t]
    .
      replace h: 173 = 111 * a := by linarith
      have o: 111 ∣ 173 := by
        zify
        rw [h]
        simp
      norm_num at o
      