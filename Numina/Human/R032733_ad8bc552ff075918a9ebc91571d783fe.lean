import Mathlib
open Real
/- 11. (22 points) Prove: For any real numbers $a, b, c$, we have
$$
\begin{array}{l}
\sqrt{a^{2}+a b+b^{2}}+\sqrt{a^{2}+a c+c^{2}} \\
\geqslant \sqrt{3 a^{2}+(a+b+c)^{2}},
\end{array}
$$

and find the necessary and sufficient conditions for equality to hold. -/
theorem inequalities_272484 (a b c : ℝ) : √(a^2 + a * b + b^2) + √(a^2 + a * c + c^2) ≥ √(3 * a^2 + (a + b + c)^2) ∧
(√(a^2 + a * b + b^2) + √(a^2 + a * c + c^2) = √(3 * a^2 + (a + b + c)^2) ↔ ((a = 0 ∧ b * c ≥ 0) ∨ b = c)):= by
  -- Define substitution variables to simplify the expressions
  set x:= a + b / 2 with hx
  set y:= √3 / 2 * b with hy
  set z:= a + c / 2 with hz
  set w:= √3 / 2 * c with hw
  clear_value x y z w

  -- Rewrite the first square root expression using the substitution variables
  rw [show a ^ 2 + a * b + b ^ 2 = x ^ 2 + y ^ 2 by rw [hx, hy] ; ring_nf ; field_simp ; linarith]
  -- Rewrite the second square root expression using the substitution variables
  rw [show a ^ 2 + a * c + c ^ 2 = z ^ 2 + w ^ 2 by rw [hz, hw] ; ring_nf ; field_simp ; linarith]
  -- Rewrite the right side of the inequality using the substitution variables
  rw [show 3 * a ^ 2 + (a + b + c) ^ 2 = (x + z) ^ 2 + (y + w) ^ 2 by rw [hx, hy, hz, hw] ; ring_nf ; field_simp ; ring_nf]

  -- Split the proof into two parts: the inequality and the equality conditions
  constructor

  -- First part: Prove the inequality
  .
    -- Express the left side as an absolute value (which is redundant since it's non-negative)
    rw [show √(x ^ 2 + y ^ 2) + √(z ^ 2 + w ^ 2) = |√(x ^ 2 + y ^ 2) + √(z ^ 2 + w ^ 2)| by exact Eq.symm (abs_of_nonneg (by positivity))]
    -- Express the right side as an absolute value (also redundant)
    rw [show √((x + z) ^ 2 + (y + w) ^ 2) = |√((x + z) ^ 2 + (y + w) ^ 2)| by exact Eq.symm (abs_of_nonneg (by positivity))]
    -- Square both sides to simplify the inequality
    suffices (√(x ^ 2 + y ^ 2) + √(z ^ 2 + w ^ 2)) ^ 2 ≥ (√((x + z) ^ 2 + (y + w) ^ 2)) ^ 2 by exact sq_le_sq.mp this
    field_simp
    ring_nf
    field_simp
    -- Reduce to proving that the product of square roots is greater than the dot product
    suffices √(x ^ 2 + y ^ 2) * √(z ^ 2 + w ^ 2) ≥ x * z + y * w by linarith
    -- Use the fact that absolute value is greater than or equal to the value itself
    have g1 : |x * z + y * w| ≥ x * z + y * w:= by exact le_abs_self (x * z + y * w)
    -- Further reduce to proving the product of norms is greater than the absolute value of dot product
    suffices √(x ^ 2 + y ^ 2) * √(z ^ 2 + w ^ 2) ≥ |x * z + y * w| by linarith
    -- Rewrite the product of square roots
    rw [show √(x ^ 2 + y ^ 2) * √(z ^ 2 + w ^ 2) = √((x ^ 2 + y ^ 2) * (z ^ 2 + w ^ 2)) by field_simp]
    -- Express as absolute value (redundant)
    rw [show √((x ^ 2 + y ^ 2) * (z ^ 2 + w ^ 2)) = |√((x ^ 2 + y ^ 2) * (z ^ 2 + w ^ 2))| by exact Eq.symm (abs_of_nonneg (by positivity))]
    -- Square both sides again
    suffices √((x ^ 2 + y ^ 2) * (z ^ 2 + w ^ 2)) ^ 2 ≥ (x * z + y * w) ^ 2 by exact sq_le_sq.mp this
    field_simp
    ring_nf
    field_simp
    -- Use the fact that squares are non-negative to complete the inequality proof
    have g2 : (x * w - y * z) ^ 2 ≥ 0:= by positivity
    linarith

  -- Second part: Prove the necessary and sufficient conditions for equality
  .
    constructor

    -- Forward direction: If equality holds, then either a=0 and b*c≥0, or b=c
    .
      intro h
      -- Start with the equality assumption
      replace h : (√(x ^ 2 + y ^ 2) + √(z ^ 2 + w ^ 2)) ^ 2 = √((x + z) ^ 2 + (y + w) ^ 2) ^ 2:= by rw [h]
      field_simp at h
      ring_nf at h
      field_simp at h
      -- Derive that the product of norms equals the dot product
      replace h : √(x ^ 2 + y ^ 2) * √(z ^ 2 + w ^ 2) = x * z + y * w:= by linarith
      -- Show that the dot product is non-negative
      have h1 : x * z + y * w ≥ 0:= by rw [←h] ; positivity
      -- Square both sides
      replace h : (√(x ^ 2 + y ^ 2) * √(z ^ 2 + w ^ 2)) ^ 2 = (x * z + y * w) ^ 2:= by rw [h]
      ring_nf at h
      field_simp at h
      -- Derive that the cross product term must be zero
      replace h : (x * w - y * z) ^ 2 = 0:= by linarith
      simp at h
      -- Substitute the original variables back
      subst x y z w
      ring_nf at h h1
      -- Simplify the cross product equation
      rw [show a * b * √3 * (-1 / 2) + a * √3 * c * (1 / 2) = √3 / 2 * a * (c - b) by linarith] at h
      simp at h
      -- Case analysis on the simplified equation
      rcases h with h | h
      .
        -- Case 1: a = 0
        left
        subst a
        simp at h1
        field_simp at h1
        ring_nf at h1
        simp
        exact h1
      .
        -- Case 2: b = c
        right
        linarith

    -- Reverse direction: If either a=0 and b*c≥0, or b=c, then equality holds
    .
      intro h
      rcases h with h | h
      .
        -- Case 1: a = 0 and b*c ≥ 0
        rcases h with ⟨h1, h2⟩
        subst a x y z w
        simp
        field_simp
        ring_nf
        field_simp
        ring_nf
        -- Rewrite squares to simplify expressions
        rw [show b ^ 2 * 4 = (2 * b) ^ 2 by ring, show c ^ 2 * 4 = (2 * c) ^ 2 by ring]
        rw [show (b * c * 8 + (2 * b) ^ 2 + (2 * c) ^ 2) = (2 * (b + c)) ^ 2 by ring]
        -- Rewrite square roots of squares as absolute values
        rw [show √((2 * b) ^ 2) = |2 * b| by exact sqrt_sq_eq_abs (2 * b)]
        rw [show √((2 * c) ^ 2) = |2 * c| by exact sqrt_sq_eq_abs (2 * c)]
        rw [show √((2 * (b + c)) ^ 2) = |2 * (b + c)| by exact sqrt_sq_eq_abs (2 * (b + c))]
        -- Case analysis on b
        by_cases hb : b = 0
        .
          -- Subcase: b = 0
          subst b
          simp
        .
          -- Subcase: b ≠ 0
          replace hb : b < 0 ∨ b > 0:= by exact lt_or_gt_of_ne hb
          rcases hb with hb | hb
          .
            -- Subcase: b < 0
            replace h2 : c ≤ 0:= by exact nonpos_of_mul_nonneg_right h2 hb
            rw [abs_of_nonpos (by linarith)]
            rw [abs_of_nonpos (by linarith)]
            rw [abs_of_nonpos (by linarith)]
            linarith
          .
            -- Subcase: b > 0
            replace h2 : c ≥ 0:= by exact nonneg_of_mul_nonneg_right h2 hb
            rw [abs_of_nonneg (by linarith)]
            rw [abs_of_nonneg (by linarith)]
            rw [abs_of_nonneg (by linarith)]
            linarith
      .
        -- Case 2: b = c
        subst b x y z w
        ring_nf
        field_simp
        ring_nf
        rw [show √4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by ring] ; field_simp]
