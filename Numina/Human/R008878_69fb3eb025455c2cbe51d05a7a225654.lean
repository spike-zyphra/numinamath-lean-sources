import Mathlib

/- Let $a,$ $b,$ $c,$ $d$ be positive real numbers such that
\begin{align*}
(a + b)(c + d) &= 143, \\
(a + c)(b + d) &= 150, \\
(a + d)(b + c) &= 169.
\end{align*}Find the smallest possible value of $a^2 + b^2 + c^2 + d^2.$ -/
theorem algebra_21585 :
    IsLeast {x | ∃ a b c d : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
      (a + b) * (c + d) = 143 ∧ (a + c) * (b + d) = 150 ∧
        (a + d) * (b + c) = 169 ∧ x = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2} 214 := by
  -- Two goals to prove:
  -- 1. 214 can be achieved
  -- 2. Any possible value is at least 214
  constructor
  . -- Set a = (13 + √19 + √26) / 2, b = (13 - √19 + √26) / 2, c = (13 + √19 - √26) / 2, d = (13 - √19 - √26) / 2
    use (13 + √19 + √26) / 2, (13 - √19 + √26) / 2, (13 + √19 - √26) / 2, (13 - √19 - √26) / 2
    -- Simple inequalities
    have h1 : √19 > 0 := by positivity
    have h2 : √19 < 5 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    have h3 : √26 > 0 := by positivity
    have h4 : √26 < 6 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    -- Enough to show that a, b, c, d are positive
    refine ⟨by linarith, by linarith, by linarith, by linarith, ?_⟩
    clear * -
    -- Prove the equalities respectively
    refine ⟨?_, ?_, ?_, ?_⟩
    . -- (a + b)(c + d) = 143
      ring_nf
      simp
      norm_num
    . -- (a + c)(b + d) = 150
      ring_nf
      simp
      norm_num
    . -- (a + d)(b + c) = 169
      ring_nf
    . -- a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 214
      ring_nf
      simp
      norm_num

  . -- Suppose a, b, c, d satisfy the conditions
    rintro x ⟨a, b, c, d, -, -, -, -, h1, h2, h3, rfl⟩
    -- We can calculate a * d + b * c, a * c + b * d, a * b + c * d from linear combinations of the given equations
    have ⟨k1, k2, k3⟩ : a * d + b * c = 62 ∧ a * c + b * d = 81 ∧ a * b + c * d = 88 := by refine ⟨?_, ?_, ?_⟩ <;> linarith
    calc a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2
         -- Expand the square in (a + b + c + d) ^ 2
         _ = (a + b + c + d) ^ 2 - (2 * (a * d + b * c) + 2 * (a * c + b * d) + 2 * (a * b + c * d)) := by ring
         -- Plug in the values of a * d + b * c, a * c + b * d, a * b + c * d
         _ = (a + b + c + d) ^ 2 - (2 * 62 + 2 * 81 + 2 * 88) := by rw [k1, k2, k3]
         -- Simplify
         _ = (a + b + c + d) ^ 2 - 462 := by norm_num
         -- (a + b + c + d) ^ 2 ≥ (a + d) * (b + c) * 4 from AM-GM
         _ ≥ (a + d) * (b + c) * 4 - 462 := by linarith only [sq_nonneg (a + d - b - c)]
         -- Plug in the value of (a + d) * (b + c)
         _ = 169 * 4 - 462 := by rw [h3]
         -- Simplify
         _ = 214 := by norm_num
