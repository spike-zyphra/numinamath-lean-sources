import Mathlib

/- If the GCD of $a$ and $b$ is $12$ and the LCM of $a$ and $b$ is $168$, what is the value of $a\times b$?

[i]2016 CCA Math Bonanza L1.3[/i] -/
theorem number_theory_38027 {a b : ℕ} (hab : a.gcd b = 12 ∧ Nat.lcm a b = 168) :
    a * b = 2016 := by
  -- Given: $\text{gcd}(a, b) = 12$
  have := Nat.gcd_mul_lcm a b -- Calculate $a \times b$
  all_goals
    aesop -- sqflies away possible goals naturally