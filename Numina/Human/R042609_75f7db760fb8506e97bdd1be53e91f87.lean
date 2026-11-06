import Mathlib

/-Find the value of $r$ such that \[\frac{r^2 - 5r + 4}{r^2-8r+7} = \frac{r^2 - 2r -15}{r^2 -r - 20}.\]-/
theorem algebra_14481 {r : ℝ} (rne1 : r - 1 ≠ 0)(rne5 : r - 5 ≠ 0):
(r^2 - 5 * r + 4) / (r^2 - 8 * r + 7) = (r^2 - 2 * r - 15) / (r^2 - r - 20) ↔
r = -5 / 4 := by
-- Break "iff" and simplify the equation
  constructor
  · rw [show r^2 - 5 * r + 4=(r-4)*(r-1) by ring, show r^2 - 8 * r + 7=(r-7)*(r-1) by ring]
    rw [show r^2 - 2 * r - 15=(r-5)*(r+3) by ring, show (r^2 - r - 20)=(r-5)*(r+4) by ring]
    rw [mul_div_mul_left, mul_div_mul_right]; intro h
    rw [div_eq_div_iff] at h; ring_nf at h
-- Solve for $r$
    apply_fun (fun x => -(x - r ^ 2 + 21)/4) at h; ring_nf at h
    linarith
    intro hr; rw [sub_eq_zero] at hr; rw [hr] at h; norm_num at h
    intro hr; rw [add_eq_zero_iff_eq_neg] at hr; rw [hr] at h; norm_num at h
    any_goals assumption
-- Conversely, check that $r=-5/4$ satisfies the equation
  intro h; rw [h]; norm_num