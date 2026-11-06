import Mathlib
/- 9. (16 points) Given that $a$, $b$, and $c$ are positive real numbers, satisfying $a+b+c=1$. Prove:
$$
\left(a^{2}+b^{2}+c^{2}\right)\left(\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\right) \geqslant \frac{1}{2} .
$$ -/
theorem inequalities_202307 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (a ^ 2 + b ^ 2 + c ^ 2) * (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 1 / 2 := by
  -- First, we prove that a² + b² + c² ≥ 1/3 using the Cauchy-Schwarz inequality
  have h1 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 1 / 3 := by
    -- We use the fact that squares of differences are non-negative
    have _ : (b - c) ^ 2 ≥ 0 := sq_nonneg (b - c)
    have _ : (c - a) ^ 2 ≥ 0 := sq_nonneg (c - a)
    nlinarith [sq_nonneg (a + b + c - 1)]
  -- Next, we prove that a/(b+c) + b/(c+a) + c/(a+b) ≥ 3/2
  have h2 : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
    -- Redundant statement of the same inequality
    have h3 : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
      -- We prove that the difference between the expression and 3/2 is non-negative
      have h4 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) ≥ 0 := by
        -- Another redundant statement
        have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
          -- We rewrite the expression in terms of squared differences
          have h6 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
            ( (a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) + (c - a) ^ 2 * (c + a) ) /
            (2 * (b + c) * (c + a) * (a + b)) := by
            -- Simplify using field operations and ring normalization
            field_simp
            ring_nf
          rw [h6]
          -- Establish that all squared differences are non-negative
          have h7 : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
          have h8 : (b - c) ^ 2 ≥ 0 := sq_nonneg (b - c)
          have h9 : (c - a) ^ 2 ≥ 0 := sq_nonneg (c - a)
          -- Products of non-negative terms with positive sums are non-negative
          have h10 : (a - b) ^ 2 * (a + b) ≥ 0 := mul_nonneg h7 (by linarith)
          have h11 : (b - c) ^ 2 * (b + c) ≥ 0 := mul_nonneg h8 (by linarith)
          have h12 : (c - a) ^ 2 * (c + a) ≥ 0 := mul_nonneg h9 (by linarith)
          -- The denominator is positive since a, b, c are positive
          have h14 : 2 * (b + c) * (c + a) * (a + b) > 0 := by
            apply mul_pos
            apply mul_pos
            all_goals nlinarith
          -- A non-negative number divided by a positive number is non-negative
          apply div_nonneg
          · linarith
          · linarith
        linarith
      linarith
    linarith
  -- Finally, we combine the two inequalities to prove the original statement
  -- using non-linear arithmetic and the fact that squares are non-negative
  nlinarith [h1, h2, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b + c - 1)]
