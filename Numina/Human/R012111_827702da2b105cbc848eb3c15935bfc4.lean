import Mathlib

/- 6. Let $x, y, z > 0$, satisfying $x+y=xy, x+y+z=xyz$. Then the range of $z$ is ( ).
(A) $(0, \sqrt{3}]$
(B) $(1, \sqrt{3}]$ -/

theorem algebra_179054 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x + y = x * y) (h2 : x + y + z = x * y * z) :
    1 < z ∧ z ≤ 4 / 3 := by
  -- express y from h1
  have hy': y * (x-1) = x := by linarith
  apply congr_arg (fun t => t/(x-1)) at hy'
  -- we need to check if x=1
  cases' eq_or_ne x 1 with xe1 xne1
  · rw [xe1] at h1 h2; simp at h1 h2
  rw [← mul_div, div_self (by simp; intro h; apply xne1; linarith), mul_one] at hy'
  -- given that y is positive we can even show 1 < x
  have h3 : 1 < x := by
    rw [hy'] at hy
    apply div_pos_iff.mp at hy
    cases' hy with hy hy <;> linarith
  -- let's express z from h2
  have h4 : z*(x*y-1) = x + y := by linarith
  apply congr_arg (fun t => t/(x*y-1)) at h4
  -- we need to check if x*y=1, simplest way: show 1 < y
  have h5 : 1 < y := by
    rw [hy']
    refine (one_lt_div ?_).mpr ?_ <;> linarith
  rw [← mul_div, div_self (by apply ne_of_gt; nlinarith), mul_one] at h4
  -- we modify the expression for z
  conv_rhs at h4 =>
    calc _
    _ = x*y/(x*y-1) := by rw [h1]
    _ = (1-1/(x*y))⁻¹ := by ring_nf; field_simp; ring_nf
    _ = (1-1/x+1/x^2)⁻¹ := by rw [hy']; ring_nf; simp; field_simp; ring_nf
  -- we can easily show that 0 < 1/x < 1
  have h6 : 0 < 1 / x := one_div_pos.mpr hx
  have h7 : 1 / x < 1 := Bound.div_lt_one_of_pos_of_lt hx h3
  -- this allows us to complete the goal
  constructor
  nlinarith
  rw [h4]
  refine (inv_le_iff_one_le_mul₀ ?_).mpr ?_
  apply add_pos_of_pos_of_nonneg
  linarith
  apply div_nonneg
  norm_num
  nlinarith
  suffices 3/4 ≤ 1 - 1 / x + 1 / x ^ 2 by linarith
  rw [show 1 - 1 / x + 1 / x ^ 2 = 3/4 + (1/2-x⁻¹)^2 by ring_nf]
  nlinarith