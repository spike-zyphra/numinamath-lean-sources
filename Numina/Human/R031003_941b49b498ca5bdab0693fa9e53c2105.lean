import Mathlib

open Real

/- Prouver que, pour tout réel $a \geqslant 0$, on a

$$
a^{3}+2 \geqslant a^{2}+2 \sqrt{a}
$$ -/
theorem inequalities_607510 (a : ℝ) (ha : 0 ≤ a) : a ^ 3 + 2 ≥ a ^ 2 + 2 * √a := by
-- Denote $t$ to be the square root of $a$ and prove that $t$ is nonnegative
  set t := √a with ht; have tge : 0 ≤ t := by positivity
  apply_fun fun x => x ^ 2 at ht; nth_rw 2 [pow_two] at ht
-- Rewrite the inequality in question in terms of $t$
  rw [mul_self_sqrt ha] at ht; rw [ge_iff_le, ← sub_nonneg, ← ht]
-- Factorize the RHS
  rw [show (t ^ 2) ^ 3 + 2 - ((t ^ 2) ^ 2 + 2 * t) = (t - 1) * (t ^ 4 * (t + 1) - 2) by ring]
-- Split the goal to two cases when $t$ is less than $1$ or not
  by_cases h : t ≤ 1
  -- In the first case, use mul_nonneg_of_nonpos_of_nonpos to finish the goal
  · apply mul_nonneg_of_nonpos_of_nonpos; linarith
    rw [sub_nonpos, show (2:ℝ) = 1*2 by simp]; apply mul_le_mul
    apply pow_le_one₀; all_goals linarith
-- In the second case, use mul_nonneg to finish the goal
  apply mul_nonneg; linarith; rw [sub_nonneg, show (2:ℝ) = 1*2 by simp]; apply mul_le_mul
  apply one_le_pow₀; any_goals linarith
  positivity