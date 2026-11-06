import Mathlib

open Real

/- 1. Let $n$ be a natural number, $a, b$ be positive real numbers, and satisfy the condition $a+b=2$, then the minimum value of $\frac{1}{1+a^{n}}+\frac{1}{1+b^{n}}$ is . $\qquad$ -/
theorem inequalities_144834 (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    1 ≤ 1 / (1 + a ^ n) + 1 / (1 + b ^ n) ∧ (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 2 ∧ 1 / (1 + a ^ n) + 1 / (1 + b ^ n) = 1) := by
    apply And.intro
    · /- Since a>0,b>0, we have (a+b)/2 ≥ √(ab). Substituting a+b=2, we get √(ab) ≤ 1, -/
      have : sqrt (a * b) ≤ 1 := by calc
        sqrt (a * b) = a ^ ((1 : ℝ) / 2) * b ^ ((1 : ℝ) / 2) :=
            by rw[sqrt_mul (by linarith), sqrt_eq_rpow, sqrt_eq_rpow]
        _ ≤ 1 / 2 * a + 1 / 2 * b  :=
            by apply geom_mean_le_arith_mean2_weighted; repeat linarith
        _ = 1 := by linarith
      -- which means ab ≤ 1
      have : a * b ≤ 1 := by simp_all only [sqrt_le_one]
      -- and therefore a^n b^n ≤ 1
      have h : a ^ n * b ^ n ≤ 1 := by
        rw[← mul_pow, ← one_pow n]
        apply pow_le_pow_left₀
        · apply le_of_lt; exact mul_pos ha hb
        · assumption

      have ha' : a ^ n > 0 := by
        apply pow_pos
        exact ha
      have hb' : b ^ n > 0 := by
        apply pow_pos
        exact hb
      have : a ^ n * b ^ n > 0 := by
        exact mul_pos ha' hb'

      /- Thus, 1/(1 + a^n) + 1/(1 + b^n) = (1 + a^n + 1 + b^n)/(1 + a^n + b^n + a^n b^n) ≥ (1+ a^n + b^n + 1)/(1+ a^n + b^n + 1) = 1.-/
      calc
        1 = (1 + a^n + b ^n + 1) / (1 + a ^ n + b ^ n + 1) := by rw [div_self (by linarith)]
        _ ≤ (1 + a^n + b ^n + 1) / (1 + a ^ n + b ^ n + a ^ n * b ^ n) := by
            apply (div_le_div_iff_of_pos_left _ _ _).2
            repeat linarith
        _ = (1 + a^n + (1 + b ^n)) / ((1 + a ^ n) * (1 + b ^ n)) := by congr 1; linarith; linarith
        _ = 1 / (1 + a ^ n) + 1 / (1 + b ^ n) := by rw [one_div_add_one_div (by linarith) (by linarith)]
    · -- Equality holds if and only if a=b=1.
      exists 1, 1
      norm_num