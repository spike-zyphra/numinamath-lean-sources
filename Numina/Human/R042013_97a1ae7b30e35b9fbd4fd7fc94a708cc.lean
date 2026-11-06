import Mathlib

/- Three real numbers $a, b$ and $c$ are given . It is known that $a + b + c >0 , bc+ ca + ab > 0$ and $abc > 0$ . Prove that $a > 0 , b > 0$ and $c > 0$ . -/
theorem inequalities_65388 (a b c : ℝ) (ha : a + b + c > 0) (hb : b * c + c * a + a * b > 0)
    (hc : a * b * c > 0) : a > 0 ∧ b > 0 ∧ c > 0 := by 
  refine' ⟨_, _, _⟩
  all_goals
    nlinarith [mul_self_nonneg a, mul_self_nonneg b, mul_self_nonneg c]