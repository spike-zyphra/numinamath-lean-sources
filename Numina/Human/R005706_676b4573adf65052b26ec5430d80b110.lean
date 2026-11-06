import Mathlib

/- Let $a, b$ and $c$ be positive real numbers such that

$$
\begin{aligned}
a^{2}+a b+b^{2} & =9 \\
b^{2}+b c+c^{2} & =52 \\
c^{2}+c a+a^{2} & =49
\end{aligned}
$$

Compute the value of $\frac{49 b^{2}-33 b c+9 c^{2}}{a^{2}}$. -/
theorem algebra_609504 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h₁ : a ^ 2 + a * b + b ^ 2 = 9) (h₂ : b ^ 2 + b * c + c ^ 2 = 52) (h₃ : c ^ 2 + c * a + a ^ 2 = 49) :
    (49 * b ^ 2 - 33 * b * c + 9 * c ^ 2) / a ^ 2 = 52 := by
  -- By symmetry, we have ∑_cyc (a - b) * (a^2 + ab + b^2) = 0, so we add them up and get 40a - 43b + 3c = 0.
  have h₄ : 40 * a - 43 * b + 3 * c = 0 := by linear_combination (a - b) * h₁ + (b - c) * h₂ + (c - a) * h₃
  -- We find that (5b - 6a)(17b + 3c) = 0 from a linear combination of the equations.
  have h₅ : (5 * b - 6 * a) * (17 * b + 3 * c) = 0 := by linear_combination (980 * h₂ - 1040 * h₃ + (5 * b + 26 * a + 20 * c) * h₄) / 9
  -- So we have 5b - 6a = 0 because 17b + 3c > 0.
  replace h₅ : 5 * b - 6 * a = 0 := by
    simp [show 17 * b + 3 * c ≠ 0 by positivity] at h₅
    exact h₅
  -- From the two linear equations, we can solve for a, b, c up to a constant factor.
  -- That is, we have a = 15k, b = 18k, c = 58k for some k > 0.
  obtain ⟨k, rfl⟩ : ∃ k, a = 15 * k := by
    use a / 15
    cancel_denoms
  obtain rfl : b = 18 * k := by linarith only [h₅]
  obtain rfl : c = 58 * k := by linarith only [h₄]
  -- Substitute these into the final expression and simplify.
  field_simp
  ring
