import Mathlib
open Real

/- Suppose x, y, z is a geometric sequence with common ratio r and x≠y. If x, 2y, 3z is an arithmetic sequence, then r is
(A）1/4 (B) 1/3  (C) 1/2 (D) 2  (E) 4 -/
theorem algebra_97967 (x y z r : ℝ) (hy : y = x * r) (hz : z = x * r^2) (hn : x ≠ y)
(h : 2 * 2 * y = x + 3 * z) : r = 1 / 3 := by
  -- using x ≠ y = x * r to obtain r ≠ 1 and x ≠ 0
  rw [hy] at hn;simp at hn
  have h1: x=x*r ↔ x*r=x := by
    constructor<;>intro a<;>symm<;>exact a
  rw [h1,mul_right_eq_self₀] at hn;simp at hn
  let ⟨hr,hx⟩ := hn;clear h1 hn
  -- using the corollaries to simplify the main equation
  rw [hy,hz,pow_two] at h
  have h': 4*r*x=(1+3*r*r)*x:=by linarith
  simp [hx] at h'
  have hq: 3*(r*r)+(-4)*r+1=0 := by linarith
  -- solve the quadratic equation to get the answer
  rw [quadratic_eq_zero_iff (by simp) (by unfold discrim;norm_num:discrim (3:ℝ) (-4) 1 = 2 * 2)] at hq
  norm_num at hq;simp [hr] at hq;simp;exact hq