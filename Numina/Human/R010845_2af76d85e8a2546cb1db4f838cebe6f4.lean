import Mathlib

open Real

/-- if $a$ and $x$ are positive real numbers, then $2*\sqrt a \leq x + \frac a x$-/
lemma p67' {a : ℝ} (hapos : 0 < a) : ∀ (x : ℝ), 0 < x → 2 * √a ≤ x + a / x := by
  intro x hxpos
  apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 1 / 2 by linarith)
  rw [mul_add, (show 1 / 2 * (2 * √a) = √a by linarith)]
  nth_rw 1 [← mul_one a, ← div_self (show x ≠ 0 by linarith),← mul_div_assoc, mul_comm a]
  rw [mul_div_assoc,sqrt_mul,sqrt_eq_rpow, sqrt_eq_rpow]
  apply geom_mean_le_arith_mean2_weighted
  simp_all; repeat linarith
  apply div_nonneg (by linarith) (by linarith)
  ring; linarith

noncomputable def f_4079 x := (x^2 + 2 - √(x^4 + 4)) / x

/-- Let $x$ be a positive real number. Find the maximum possible value of $$\frac{x^2+2-\sqrt{x^4+4}}{x}.$$ -/
theorem intermediate_algebra_4079  : (∀ x, 0 < x → f_4079 x ≤ 2 * √2 - 2)
            ∧ ∃ x, 0 < x → f_4079 x = 2 * √2 - 2 := by
  constructor
  · intro x hxpos
    -- $$\begin{align*}
    -- \frac{x^2+2-\sqrt{x^4+4}}{x}\cdot\frac{x^2+2+\sqrt{x^4+4}}{x^2+2+\sqrt{x^4+4}}&=\frac{(x^2+2)^2-(x^4+4)}{x(x^2+2+\sqrt{x^4+4})}\\
    -- &=\frac{4x^2}{x(x^2+2+\sqrt{x^4+4})}\\
    -- &=\frac{4}{\frac{1}{x}(x^2+2+\sqrt{x^4+4})}\\
    -- &=\frac{4}{x+\frac{2}{x}+\sqrt{x^2+\frac{4}{x^2}}}.
    -- \end{align*}$$
    have : f_4079 x = 4 / (x + 2/x + √(x^2 + 4/x^2)) := by
      calc
        f_4079 x = (x^2 + 2 - √(x^4 + 4)) / x * 1 := by dsimp [f_4079]; ring
        _ = (x^2 + 2 - √(x^4 + 4)) / x * ((x^2 + 2 + √(x^4 + 4)) / (x^2 + 2 + √(x^4 + 4))) := by
          rw [← div_self]
          apply ne_of_gt
          repeat
            rw [← zero_add 0]
            apply add_lt_add_of_lt_of_lt
          · simp_all
          · simp_all
          · apply sqrt_pos_of_pos
            rw [← zero_add 0]
            apply add_lt_add_of_lt_of_lt
            repeat simp_all
        _ = ((x^2 + 2 - √(x^4 + 4)) * (x^2 + 2 + √(x^4 + 4))) / (x*(x^2 + 2 + √(x^4 + 4))) := by simp_all [div_mul_div_comm]
        _ = 4 * x^2 / (x*(x^2 + 2 + √(x^4 + 4))) := by
          rw [mul_comm, ← sq_sub_sq (x^2 + 2) √(x^4 + 4),sq_sqrt]
          rw [add_pow_two,← pow_mul, (show 2 * 2 = 4 by norm_num)]
          rw [(show 2 * x ^ 2 *2 = 4 * x^2 by ring), (show 2 ^ 2 = (4 : ℝ) by norm_num)]
          simp_all
          rw [← zero_add 0]
          apply add_le_add
          rw [(show x ^ 4 = (x^2)^2 by ring)]
          exact pow_two_nonneg (x^2)
          simp_all
        _ = 4 * x / (x^2 + 2 + √(x^4 + 4)) := by
          rw [pow_two, ← mul_assoc 4,← mul_comm,mul_div_mul_left]
          linarith
        _ = 4 / (x + 2/x + √(x^4 + 4)/x) := by
          nth_rw 1 [← inv_inv x,← div_eq_mul_inv,div_div,mul_comm x⁻¹]
          rw [← div_eq_mul_inv,add_div,add_div,pow_two,mul_self_div_self]
        _ = 4 / (x + 2/x + √((x^4 + 4)/x^2)) := by
          rw [← sqrt_sq (show 0 ≤ x by linarith), ← sqrt_div,sqrt_sq]
          linarith
          rw [← zero_add 0]
          apply add_le_add
          rw [(show 4 = 2 * 2 by norm_num),pow_mul]
          exact pow_two_nonneg (√(x ^ 2) ^ 2)
          linarith
        _ = 4 / (x + 2/x + √(x^2 + 4/x^2)) := by
          rw [add_div,(show 4 = 2 + 2 by norm_num),pow_add,mul_div_assoc]
          rw [div_self,mul_one]
          simp_all; linarith
    rw [this]
    -- By AM-GM, $x+\frac 2 x \geq 2\sqrt2$ and $x^2+\frac 4 {x^2} \geq 4$.
    have h₁ : 2 * √2 ≤ x + 2 / x := by
      apply p67' (by linarith); linarith
    have h₂ : 2 ≤ √(x ^ 2 + 4 / x ^ 2) := by
      rw [(show 2 = √(2^2) by aesop)]
      apply sqrt_le_sqrt
      rw [(show 2^2 = (2 : ℝ) * 2 by ring)]
      nth_rw 2 [← sqrt_sq (show 0 ≤ 2 by linarith)]
      rw [(show 2^2 = (4 : ℝ) by ring)]
      apply p67' (by linarith)
      aesop
    -- So the denominator is at least $2\sqrt2 +2$.
    have h' : 2 * √2 + 2 ≤ x + 2 / x + √(x ^ 2 + 4 / x ^ 2) := by linarith
    -- Therefore, the maximum possible value of $2*\sqrt a \leq x + \frac a x$ is $ \frac 4 {2\sqrt2 +2} = 2\sqrt2 - 2$.
    have h'' : 2 * √2 - 2 = 4 / (2*√2 + 2) := by
      apply Eq.symm
      calc
        4 / (2*√2 + 2) = 4 * (2*√2 - 2) / ((2*√2 + 2) * (2*√2 - 2)) := by
          apply Eq.symm
          apply mul_div_mul_right
          rw [sub_ne_zero]
          aesop
        _ = 4 * (2*√2 - 2) / 4 := by
          rw [← sq_sub_sq, mul_pow, (show 2^2 = (4 : ℝ) by linarith)]
          rw [sq_sqrt, (show (4 * 2 - 4) = (4 : ℝ) by ring)]
          linarith
        _ = 2*√2 - 2 := by simp
    rw [h'']
    apply div_le_div_of_nonneg_left (by linarith)
    rw [← zero_add 0]
    apply add_lt_add (by simp_all) (by linarith)
    exact h'
  · -- when $x=\sqrt 2$, the equality holds.
    use √2
    intro _; dsimp [f_4079]
    rw [sq_sqrt (by linarith),(show 4 = 2 + 2 by linarith),pow_add]
    rw [sq_sqrt (show 0 ≤ 2 by linarith), (show 2 * 2 = (4 : ℝ) by norm_num)]
    rw [(show 4 + 4 = (8 : ℝ) by norm_num), (show 2 + 2 = (4 : ℝ) by norm_num)]
    rw [(show (8 : ℝ) = 2 * 2^2 by ring), sqrt_mul (by linarith),sqrt_sq (by linarith)]
    rw [(show (4 : ℝ) = 2 * 2 by ring)]
    nth_rw 1 [(show 2 = √2 * √2 by norm_num), mul_assoc, ← mul_sub √2]
    norm_num; ring
