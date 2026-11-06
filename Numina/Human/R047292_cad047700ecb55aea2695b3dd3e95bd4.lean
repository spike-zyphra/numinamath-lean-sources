import Mathlib
/- 164. Prove that if

$$
|a-b| \geq|c|, \quad|b-c| \geq|a|, \quad|c-a| \geq|b|
$$

then one of the numbers $a, b$, and $c$ is equal to the sum of the other two. -/
theorem inequalities_187774 {a b c : ℝ} (h1 : |a - b| ≥ |c|) (h2 : |b - c| ≥ |a|) (h3 : |c - a| ≥ |b|) : a = b + c ∨ b = a + c ∨ c = a + b:= by
  -- Convert absolute value inequalities to squared inequalities
  apply sq_le_sq.mpr at h1
  apply sq_le_sq.mpr at h2
  apply sq_le_sq.mpr at h3

  -- Rewrite the squared inequalities as products of factors
  replace h1 : (a - b - c) * (a - b + c) ≥ 0:= by linarith
  replace h2 : (b - c - a) * (b - c + a) ≥ 0:= by linarith
  replace h3 : (c - a - b) * (c - a + b) ≥ 0:= by linarith

  -- Combine the inequalities using multiplication
  replace h1:= mul_nonneg h1 h2
  replace h1:= mul_nonneg h1 h3

  -- Rewrite the product using ring normalization to show it equals a negative expression
  rw [show (a - b - c) * (a - b + c) * ((b - c - a) * (b - c + a)) * ((c - a - b) * (c - a + b)) = - (a - b - c) ^ 2 * (b - c - a) ^ 2 * (c - a - b) ^ 2 by ring_nf] at h1

  -- Establish that the squared expression is non-negative
  have h4 : (a - b - c) ^ 2 * (b - c - a) ^ 2 * (c - a - b) ^ 2 ≥ 0:= by positivity

  -- Deduce that the expression must equal zero
  replace h4 : (a - b - c) ^ 2 * (b - c - a) ^ 2 * (c - a - b) ^ 2 = 0:= by linarith

  -- Simplify to get that one of the factors must be zero
  simp at h4

  -- Case analysis on which factor equals zero
  rcases h4 with ⟨h4 | h4⟩ | h4
  .
    -- Case 1: a - b - c = 0, which means a = b + c
    left
    linarith
  .
    -- Case 2: b - c - a = 0, which means b = a + c
    right
    left
    linarith
  .
    -- Case 3: c - a - b = 0, which means c = a + b
    right
    right
    linarith
