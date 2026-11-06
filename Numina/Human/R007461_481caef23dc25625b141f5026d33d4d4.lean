import Mathlib

/- Problem 1. Let $a, b, c$ be strictly positive real numbers. Show that


$$

\frac{1}{a b c}+1 \geq 3\left(\frac{1}{a^{2}+b^{2}+c^{2}}+\frac{1}{a+b+c}\right)

$$
 -/
theorem inequalities_103505 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / a / b / c + 1 ≥ 3 * (1 / (a ^ 2 + b ^ 2 + c ^ 2) + 1 / (a + b + c)) := by
  -- use am-gm ineq for n = 3 on a^2, b^2, c^2 and a, b, c
  have h₁ : ((a * b * c) ^ (1/3:ℝ)) ^ 2 ≤ (a^2 + b^2 + c^2)/3 := by
    have : 0 ≤ (1/3:ℝ) := by norm_num
    have := Real.geom_mean_le_arith_mean3_weighted this this this (show 0 ≤ a^2 by positivity) (show 0 ≤ b^2 by positivity) (show 0 ≤ c^2 by positivity) (by norm_num)
    convert this using 1
    . repeat rw [← Real.rpow_natCast]
      repeat rw [← Real.rpow_mul (by positivity)]
      ring_nf
      repeat rw [Real.mul_rpow (by positivity) (by positivity)]
    . ring
  have h₂ : (a * b * c) ^ (1/3:ℝ) ≤ (a + b + c)/3 := by
    have : 0 ≤ (1/3:ℝ) := by norm_num
    have := Real.geom_mean_le_arith_mean3_weighted this this this (show 0 ≤ a by positivity) (show 0 ≤ b by positivity) (show 0 ≤ c by positivity) (by norm_num)
    convert this using 1
    . repeat rw [Real.mul_rpow (by positivity) (by positivity)]
    . ring
  -- invert the last two inequalities
  have h₃ : 3 / (a^2 + b^2 + c^2) ≤ 1 / ((a * b * c) ^ (1/3:ℝ)) ^ 2 := by
    apply le_of_one_div_le_one_div
    . positivity
    . linarith
  have h₄ : 3 / (a + b + c) ≤ 1 / (a * b * c) ^ (1/3:ℝ) := by
    apply le_of_one_div_le_one_div
    . positivity
    . linarith
  -- prove an auxiliary lemma t^2 + t ≤ t^3 + 1 for nonegative t by factoring it
  have h₅ {t : ℝ} (ht: 0 ≤ t) : t^2 + t ≤ t^3 + 1 := by linarith [show (t - 1)^2 * (t + 1) ≥ 0 by positivity]
  -- now the lemma applied on (1 / (abc)^(1/3)) provides following inequality
  have h₆ : 1 / ((a * b * c) ^ (1/3:ℝ)) ^ 2 + 1 / (a * b * c) ^ (1/3:ℝ) ≤ 1 / (a * b * c) + 1 := by
    convert h₅ (show 0 ≤ 1 / (a * b * c) ^ (1 / 3 : ℝ) by positivity) using 2
    . simp
    . rw [← Real.rpow_natCast]
      rw [Real.div_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_mul (by positivity)]
      simp
  -- the inequalities together show following inequality which is almost target
  have h₇ : 1 / (a * b * c) + 1 ≥ 3 / (a ^ 2 + b ^ 2 + c ^ 2) + 3 / (a + b + c) := by linarith
  -- show it is target by fixing the terms
  convert h₇ using 1
  . field_simp
  . ring