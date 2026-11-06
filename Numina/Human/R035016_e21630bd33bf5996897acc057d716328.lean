import Mathlib

open Real Set
open scoped Real

/- Example 5 Find the maximum value of the function $y=2 \sin \frac{x}{2}\left(1-\sin \frac{x}{2}\right)\left(1+\sin \frac{x}{2}\right)^{2}, x \in(0, \pi)$. -/
theorem algebra_241493 :
    IsGreatest { 2 * sin (x / 2) * (1 - sin (x / 2)) * (1 + sin (x / 2)) ^ 2 | (x : ℝ) (_ : 0 ≤ x) (_ : x ≤ π)} ((107 + 51 * √17)/256) := by
  -- write powers of √17 as they'll be useful later
  have h17_3 : √17 ^ 3 = 17 * √ 17 := by rw [pow_three, ← pow_two]; simp; ring
  have h17_4 : √17 ^ 4 = 17 * 17 := by rw [pow_succ, h17_3, mul_assoc, ← pow_two]; simp
  constructor <;> simp
  -- first prove that using x = 2 * arcsin ((1 + √17) / 8), we get the value
  . use 2 * arcsin ((1 + √17) / 8)
    and_intros
    . linarith [pi_pos, arcsin_le_pi_div_two ((1 + √17) / 8)]
    . simp; positivity
      -- prove bounds on (1 + √17) / 8 to make sure we can replace sin(arcsin(x)) by x
    . rw [show 2 * arcsin ((1 + √17) / 8) / 2 = arcsin ((1 + √17) / 8) by ring]
      have h₁ : ((1 + √17) / 8) ≤ 1 := by
        nth_rw 2 [show (1 : ℝ) = (1 + 7) / 8 by norm_num]
        gcongr
        apply sq_le_sq₀ (by positivity) (by positivity) |>.mp
        norm_num
      have h₂ : -1 ≤ ((1 + √17) / 8) := by
        suffices 0 ≤ (1 + √17) / 8 by linarith
        positivity
      rw [sin_arcsin h₂ h₁]
      ring_nf
      rw [h17_3, h17_4]
      ring_nf; simp
      ring
  -- no proving upper bound
  . rintro y ⟨x, hx_lb, hx_ub, hy⟩
    rw [← hy]
    -- define constants a, b which will help us use am-gm
    let a := (1 + √17) / 2
    let b := (5 + √17) / 2
    have : a > 0 := by positivity
    have : b > 0 := by positivity
    -- prove bounds on sin (x/2) which will help positivity later
    have : sin (x / 2 ) ≥ 0 := by refine sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have : 1 - sin (x / 2) ≥ 0 := by linarith [sin_le_one (x / 2)]
    calc
      -- first right target as product of 4 terms
      _ = 2 / (a * b) * ((a * sin (x/2)) * (b * (1 - sin (x/2))) * (1 + sin (x/2)) * (1 + sin (x/2))) := by
        field_simp
        ring
      -- use 4 variable am-gm on those 4 variables
      _ ≤ 2 / (a * b) * ((a * sin (x/2) + b * (1 - sin (x/2)) + (1 + sin (x/2)) + (1 + sin (x/2))) / 4) ^ 4 := by
        gcongr
        have : (0 : ℝ) ≤ 1 / 4 := by norm_num
        have ineq := geom_mean_le_arith_mean4_weighted this this this this
          (show 0 ≤ a * sin (x / 2) by positivity) (show 0 ≤ b * (1 - sin (x / 2)) by positivity)
          (show 0 ≤ (1 + sin (x/2)) by positivity) (show 0 ≤ (1 + sin (x/2)) by positivity) (by norm_num)
        repeat rw [← mul_rpow (by positivity) (by positivity)] at ineq
        replace ineq := pow_le_pow_left₀ (by positivity) ineq 4
        convert ineq using 1
        . rw [← rpow_natCast, ← rpow_mul (by positivity)]
          simp
        . ring
      -- simplifiying takes out the sin
      _ = 2 / (a * b) * ((b + 2) / 4) ^ 4 := by ring
      -- now express the expression so that a * b can be cancelled
      _ = 2 / (a * b) * (a * b * (107 + 51 * √17) / 512) := by
        congr
        simp [a, b]
        ring_nf; simp
        rw [h17_3, h17_4]
        ring
      -- simplify
      _ = ((107 + 51 * √17)/256) := by
        field_simp
        ring