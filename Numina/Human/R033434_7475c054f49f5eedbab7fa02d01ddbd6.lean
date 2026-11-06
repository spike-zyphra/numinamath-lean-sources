import Mathlib

/- 3. For positive real numbers $a, b, c$ it holds that


$$

a b+b c+c a=16, \quad a \geqq 3 .

$$


Find the smallest possible value of the expression $2 a+b+c$. -/
theorem algebra_260151 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 16) (h1 : a ≥ 3) : 2 * a + b + c ≥ 10 := by

      --First, show (2 * a + b + c)^2 = 4 * a^2 + (b - c)^2 + 4 * (a * b + b * c + c * a).
      have h1' : (2 * a + b + c)^2 = 4 * a^2 + (b - c)^2 + 4 * (a * b + b * c + c * a):= by
        ring

      --Then show (2 * a + b + c)^2 = 4 * a^2 + (b - c)^2 + 4 * 16.
      have h2 : (2 * a + b + c)^2 = 4 * a^2 + (b - c)^2 + 4 * 16 := by
        rw [←h]; ring

      --Next, show (b - c)^2 ≥ 0.
      have h3 : (b - c)^2 ≥ 0 := by exact sq_nonneg (b - c)

      --Obtain a^2 ≥ 3^2.
      have h4 : a^2 ≥ 3^2 := by
        apply pow_le_pow_left₀
        . norm_num
        . exact h1
      
      --2 * a + b + c ≥ 10
      have h5 : 2 * a + b + c ≥ 10 := by
        have s1 : 0 ≤ 2 * a + b + c := by positivity
        have s2 : 10^2 ≤ (2 * a + b + c)^2 := by linarith
        exact le_of_sq_le_sq s2 s1

      exact h5