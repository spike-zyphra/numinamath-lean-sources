import Mathlib

open Real
/-Let x < y be positive real numbers such that
√x + √y = 4 and √(x+2) + √(y+2) = 5. Compute x.-/
theorem algebra_610743 {x y: ℝ} (hxy: x < y) (hx: 0 < x) (h1: √x + √y = 4)
(h2: √(x+2) + √(y+2) = 5): x = 49/36 := by
  set a:= √x with ha
  set b:= √y with hb  -- start by eliminating y --
  have ox: x = √x ^ 2 := by   -- prove some fundamental results --
    rw [← Real.sqrt_eq_iff_eq_sq]
    linarith
    apply Real.sqrt_nonneg
  have oy: y = √y ^ 2 := by
    rw [← Real.sqrt_eq_iff_eq_sq]
    linarith
    apply Real.sqrt_nonneg
  have o1: (√(2 + a ^ 2)) ^ 2 = 2+ a ^ 2:= by
    symm
    rw [← Real.sqrt_eq_iff_eq_sq]
    linarith
    apply Real.sqrt_nonneg
  have o2: √(18 - a * 8 + a ^ 2) ^ 2 = 18 - a * 8 + a ^ 2 := by
    symm
    rw [← Real.sqrt_eq_iff_eq_sq]
    rw [show (18 - a * 8 + a ^ 2) = (a - 4) ^ 2 + 2 by ring]
    nlinarith
    apply Real.sqrt_nonneg
  rw [ox]
  rw[← ha]
  replace hxy: a < b := by
    rw [ha, hb]
    apply Real.sqrt_lt_sqrt
    linarith
    exact hxy
  rw [ox,oy] at h2
  rw [← ha,← hb] at h2
  clear hx ha hb ox oy
  clear_value a b
  replace h1: b = 4 - a := by linarith
  simp [h1] at h2
  rw [h1] at hxy
  replace hxy: a < 2 := by linarith
  clear h1
  -- simplify the equation by squaring twice --
  replace h2: (√(a ^ 2 + 2) + √((4 - a) ^ 2 + 2)) ^ 2 = 25 := by rw[h2];norm_num
  have eq: (√(a ^ 2 + 2) + √((4 - a) ^ 2 + 2)) ^ 2 = 2 * a ^ 2 - 8 * a + 20 + 2 * √(a ^ 2 + 2) * √(a ^ 2 - 8 * a + 18) := by
    ring_nf
    rw [o1,o2]
    ring
  rw [eq] at h2
  clear eq
  replace h2: 2 * √(a ^ 2 + 2) * √(a ^ 2 - 8 * a + 18) = -2 * a ^ 2 + 8 * a + 5 := by
    rw [show 2 * √(a ^ 2 + 2) * √(a ^ 2 - 8 * a + 18)
     = 2 * a ^ 2 - 8 * a + 20 + 2 * √(a ^ 2 + 2) * √(a ^ 2 - 8 * a + 18) - (2 * a ^ 2 - 8 * a + 20) by ring]
    rw [h2]
    ring
  replace h2: (2 * √(a ^ 2 + 2) * √(a ^ 2 - 8 * a + 18)) ^ 2 = (-2 * a ^ 2 + 8 * a + 5) ^ 2 := by
    rw [h2]
  have eql: (2 * √(a ^ 2 + 2) * √(a ^ 2 - 8 * a + 18)) ^ 2 = 4 * (a ^ 2 + 2) * (a ^ 2 - 8 * a + 18) := by
    ring_nf
    rw [o1,o2]
    ring
  rw [eql] at h2
  clear eql o1 o2
  replace h2: 4 * (a ^ 2 + 2) * (a ^ 2 - 8 * a + 18) - (-2 * a ^ 2 + 8 * a + 5) ^ 2 = 0 := by
    rw [h2]
    ring
  have eq: 4 * (a ^ 2 + 2) * (a ^ 2 - 8 * a + 18) - (-2 * a ^ 2 + 8 * a + 5) ^ 2 = 36 * a ^ 2 - 144 * a + 119 := by
    ring
  rw [eq] at h2
  clear eq
  have eq: 36 * a ^ 2 - 144 * a + 119 = 36 * (a - 7 / 6) * (a - 17 / 6) := by ring
  rw [eq] at h2
  clear eq
  simp at h2
  rcases h2 with h2 | h2
  . nlinarith
  . nlinarith [hxy]