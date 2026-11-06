import Mathlib

/- Solve the following equation:


$$

\log \left[\frac{1}{x}+\frac{96}{x^{2}\left(x^{2}-1\right)}\right]=\log (x+1)+\log (x+2)+\log (x+3)-2 \log x-\log \left(x^{2}-1\right)

$$
 -/
--  we add hx and hx' to formalization since lean admits negative args to Real.log but that makes the statement false
theorem algebra_231967 {x : ℝ} (hx : x > 0) (hx': x^2-1>0):
    Real.log (1 / x + 96 / (x ^ 2 * (x ^ 2 - 1))) =
    Real.log (x + 1) + Real.log (x + 2) + Real.log (x + 3) -
    2 * Real.log x - Real.log (x ^ 2 - 1) ↔ x = 3 := by
    -- from constraints we show x>1
    have hx1 : x > 1 := by
      simp at *;
      unfold abs at hx'
      simp at hx'
      cases' hx' with hxl hxr
      linarith
      linarith
    -- collect the logs
    rw [← Real.log_mul (by linarith) (by linarith),
        ← Real.log_mul (by linarith) (by linarith),
        ← Real.log_rpow (by linarith),
        ← Real.log_div (by simp; exact ⟨⟨by linarith, by linarith⟩, by linarith⟩) (by simp; linarith),
        ← Real.log_div (by simp; exact ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩, by linarith⟩) (by linarith)]
    -- left implication is easy
    constructor
    rotate_left
    intro hx; rw [hx]; norm_num
    -- right implication now
    intro h
    -- log is injective so we get rid of it
    have q:= Real.log_injOn_pos; unfold Set.InjOn Set.Ioi at q; simp at q
    have q:= q (x₁:=(1 / x + 96 / (x ^ 2 * (x ^ 2 - 1)))) (x₂:=((x + 1) * (x + 2) * (x + 3) / x ^ 2 / (x ^ 2 - 1))) (by apply add_pos; exact one_div_pos.mpr hx; apply div_pos; norm_num; apply mul_pos; linarith; assumption) (by apply div_pos; apply div_pos; apply mul_pos; apply mul_pos; linarith; linarith; linarith; norm_cast; linarith; assumption) h
    -- get rid of denominators and simplify
    apply congr_arg (fun t=>t * x^2 * (x^2-1)) at q
    conv_lhs at q =>
      calc (1 / x + 96 / (x ^ 2 * (x ^ 2 - 1))) * x ^ 2 * (x ^ 2 - 1)
      _ = x / x * x * (x ^ 2 - 1) + 96 * ((x ^ 2 * (x ^ 2 - 1))/ (x ^ 2 * (x ^ 2 - 1))) := by ring_nf
      _ = x * (x ^ 2 - 1) + 96 := by rw [div_self (by linarith), one_mul, div_self (by simp; constructor; linarith; linarith), mul_one]
    conv_rhs at q =>
      calc (x + 1) * (x + 2) * (x + 3) / x ^ (2:ℝ) / (x ^ 2 - 1) * x ^ 2 * (x ^ 2 - 1)
      _ = (x + 1) * (x + 2) * (x + 3) * (x ^ 2 / x ^ 2) * ((x ^ 2 - 1) / (x ^ 2 - 1)) := by norm_cast; ring_nf
      _ = (x + 1) * (x + 2) * (x + 3) := by rw [div_self (by linarith), div_self (by linarith), mul_one, mul_one]
    -- let's set up 0 on the right
    apply congr_arg (fun t=>(t - (x + 1) * (x + 2) * (x + 3))/6) at q
    ring_nf at q
    -- and collect the quadratic equation
    conv_lhs at q =>
      calc 15 + (-(x * 2) - x ^ 2)
      _ = -1 * (x*x)+ -2*x+15 := by ring_nf

    -- simple quadratic to solve
    have sol := (quadratic_eq_zero_iff (a:=(-1:ℝ)) (b:=(-2:ℝ)) (c:=(15:ℝ)) (by norm_num) (s:=8) (by unfold discrim; norm_num) x).mp q; norm_num at sol
    cases' sol with solneg solpos
    linarith
    assumption