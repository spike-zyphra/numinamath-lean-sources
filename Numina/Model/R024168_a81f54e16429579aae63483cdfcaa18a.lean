import Mathlib

/- Let real numbers $a$, $b$, $c$, and $d$ satisfy 
\[
\begin{cases}
\left( a+b \right)\left( c+d \right)=13 \\
\left( a+c \right)\left( b+d \right)=24 \\
\left( a+d \right)\left( b+c \right)=25 \\
\end{cases}
\]
Then the minimum possible value of ${{a}^{2}}+{{b}^{2}}+{{c}^{2}}+{{d}^{2}}$ is ___          ___. -/
theorem algebra_7230 :
    IsLeast {x | ∃ a b c d : ℝ, x = a^2 + b^2 + c^2 + d^2 ∧ (a + b) * (c + d) = 13 ∧ (a + c) * (b + d) = 24 ∧ (a + d) * (b + c) = 25} 38 := by
  constructor
  · -- Show that 38 is achievable with specific values
    use 2 + Real.sqrt 3, 3 + Real.sqrt 3, 2 - Real.sqrt 3, 3 - Real.sqrt 3
    constructor
    · -- Verify that the sum of squares equals 38
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    constructor
    · -- Verify the first equation: (a + b) * (c + d) = 13
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    constructor
    · -- Verify the second equation: (a + c) * (b + d) = 24
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- Verify the third equation: (a + d) * (b + c) = 25
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  · -- Show that 38 is the minimum possible value
    intro x hx
    rcases hx with ⟨a, b, c, d, h_eq, h1, h2, h3⟩
    have h4 : a^2 + b^2 + c^2 + d^2 ≥ 38 := by
      nlinarith [sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c), sq_nonneg (a - b + c - d), sq_nonneg (a - b - c + d), sq_nonneg (a + b + c + d)]
    linarith [h_eq, h4]