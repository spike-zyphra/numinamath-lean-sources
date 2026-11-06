import Mathlib
open Real

/-Let r be the speed in miles per hour at which a wheel, 11 feet in circumference.
travels. If the time for a complete rotation of the wheel is shortened by 1 of a
second, the speed r is increased by 5 miles per hour. Then r is:
(A) 9 (B) 10 (C) 10 (D) 11 (E) 12-/
theorem algebra_94910 (r t : ℝ) (hr : r > 0)
  (h1 : t*r=11/5280*3600) (h2:(r+5)*(t-1/4)=11/5280*3600) :
r = 10 := by
  -- using r to represent t
  have hrpos:=(by linarith:r≠0)
  rw [← div_left_inj' hrpos] at h1
  simp [hrpos] at h1
  -- substituting the expression of t, eliminating t
  rw [h1] at h2
  field_simp at h2
  -- reducing the equation to a quadratic form
  have hq:1*(r*r)+5*r+(-150)=0:=by linarith
  -- solve the quadratic equation
  rw [quadratic_eq_zero_iff (by simp) (by unfold discrim;norm_num:discrim (1:ℝ) 5 (-150) = 25 * 25)] at hq
  field_simp at hq
  -- discard the negative root
  obtain hr1 | hr2 := hq <;> linarith