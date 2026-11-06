import Mathlib

/-Given $x=-2272, y=10^{3}+10^{2} c+10 b+a, z=1$ satisfy the equation $a x+b y+c z=1$, where $a, b, c$ are positive integers, $a<b<c$, find $y$.
-/
theorem algebra_209626 {a b c x y z : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hord : a < b ∧ b < c) (h : a * x + b * y + c * z = 1) (hx : x = -2272)
    (hy : y = 10 ^ 3 + 10 ^ 2 * c + 10 * b + a) (hz : z = 1) :
    y = 1987 := by
  rw [hx, hy, hz] at h
  have h1 : a ≤ 7 := by
    by_cases h' : a ≤ 7
    · linarith
    · -- Assume a ≥ 8
      have h'a : a ≥ 8 := by omega
      nlinarith [hord.left, hord.right, h'a, show 0 ≤ b * y + c - 1 by nlinarith]
  have h2 : b ≤ 8 := by 
    nlinarith [hord.right, h1]
  have h3 : c ≤ 9 := by 
    nlinarith [hord.right, h2]
  interval_cases a <;> 
  interval_cases b <;> 
  interval_cases c <;> 
  omega