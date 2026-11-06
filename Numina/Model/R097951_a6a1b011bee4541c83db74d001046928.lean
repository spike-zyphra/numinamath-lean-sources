import Mathlib

theorem algebra_251648 {a b c : ℝ} (ha : a ≠ 0) (hroots : {x | a * x ^ 2 + b * x + c = 0} = {x1, x2})
    (hx1 : x1 > 0) (hx2 : x2 = 4 * x1) (hcoeff : 3 * a = 2 * (c - b)) :
    x1 = 1 / 4 ∧ x2 = 1 := by

  -- $x_1$ is a root of the quadratic equation
  have h1 : a * x1 ^ 2 + b * x1 + c = 0 := by
    rw [Set.ext_iff] at hroots
    specialize hroots x1
    simpa using hroots
  -- $x_2$ is a root of the quadratic equation
  have h2 : a * x2 ^ 2 + b * x2 + c = 0 := by
    rw [Set.ext_iff] at hroots
    specialize hroots x2
    simpa using hroots

  rw [hx2] at h2

  -- Subtract the equation of x1 from the equation of x2 multiplied by 16
  -- a*x1^2 +b*x1 +c =0
  -- 16*a*x1^2 +4*b*x1 +c =0
  -- Subtract:
  -- 15*a*x1^2 +3*b*x1 =0
  -- 5*a*x1^2 +b*x1 =0
  have eq2 : 5 * a * x1 ^ 2 + b * x1 = 0 := by
    nlinarith [sq_pos_of_pos (show 0 < x1 by linarith), sq_nonneg (4 * x1 - x1), sq_nonneg (4 * x1 - x1)]
  have hb : b = -5 * a * x1 := by
    have hx1_nezero : x1 ≠ 0 := by linarith
    apply (mul_left_inj' hx1_nezero).mp
    linarith

  -- Use the coefficient condition 3a=2(c-b)
  have hc : c = (3 * a - 10 * a * x1) / 2 := by
    nlinarith [hcoeff, hb]
  -- Substitute into the quadratic equation in x1
  rw [hb, hc] at h1
  -- Simplify to get the quadratic equation in x1
  have h3 : 8 * x1 ^ 2 + 10 * x1 - 3 = 0 := by
    apply (mul_left_inj' ha).mp
    nlinarith
  -- Solve the quadratic equation
  have h4 : (x1 - 1/4) * (8 * x1 + 12) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where $x1 = 1/4$
    have hx1_eq : x1 = 1 / 4 := by linarith
    have hx2_eq : x2 = 1 := by
      rw [hx2]
      nlinarith [hx1_eq]
    exact ⟨hx1_eq, hx2_eq⟩
  · -- Case where $8x1+12=0$, so $x1=-3/2<0$ contradicts with $x1>0$.
    linarith