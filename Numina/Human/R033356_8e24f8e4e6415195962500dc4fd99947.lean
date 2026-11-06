import Mathlib
/- Soient $x$ et $y$ deux réels positifs. Montrer que

$$
\left(x^{2}+x+1\right)\left(y^{2}+y+1\right) \geqslant 9 x y .
$$

Quels sont les cas d'égalité? -/
theorem algebra_607158 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x ^ 2 + x + 1) * (y ^ 2 + y + 1) ≥ 9 * x * y ∧ ((x ^ 2 + x + 1) * (y ^ 2 + y + 1) = 9 * x * y ↔ x = 1 ∧ y = 1):= by

  -- Key algebraic identity: Rewrite the difference as sum of two non-negative terms
  have h1 : (x ^ 2 + x + 1) * (y ^ 2 + y + 1) - 9 * x * y = (x - 1) ^ 2 * ((y + 1 / 2) ^ 2 + 3 / 4) + 3 * x * (y - 1) ^ 2:= by linarith
  constructor

  -- First part: Prove the inequality
  .
    suffices (x ^ 2 + x + 1) * (y ^ 2 + y + 1) - 9 * x * y ≥ 0 by linarith
    rw [h1]
    positivity

  -- Second part: Characterize equality case
  .
    constructor
    -- Forward direction: If equality holds, then x = 1 and y = 1
    .
      intro h
      replace h : (x - 1) ^ 2 * ((y + 1 / 2) ^ 2 + 3 / 4) + 3 * x * (y - 1) ^ 2 = 0:= by linarith
      -- Both terms are non-negative
      have g1 : (x - 1) ^ 2 * ((y + 1 / 2) ^ 2 + 3 / 4) ≥ 0:= by positivity
      have g2 : 3 * x * (y - 1) ^ 2 ≥ 0:= by positivity
      -- Therefore both terms must be zero
      replace g1 : (x - 1) ^ 2 * ((y + 1 / 2) ^ 2 + 3 / 4) = 0:= by linarith
      replace g2 : 3 * x * (y - 1) ^ 2 = 0:= by linarith
      -- Show that certain terms are nonzero
      have g3 : ((y + 1 / 2) ^ 2 + 3 / 4) ≠ 0:= by positivity
      have g4 : 3 * x ≠ 0:= by positivity
      -- Conclude that x - 1 = 0 and y - 1 = 0
      replace g1 : (x - 1) ^ 2 = 0:= by exact eq_zero_of_ne_zero_of_mul_right_eq_zero g3 g1
      replace g2 : (y - 1) ^ 2 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g4 g2
      replace g1 : x - 1 = 0:= by exact pow_eq_zero g1
      replace g2 : y - 1 = 0:= by exact pow_eq_zero g2
      constructor
      all_goals
      linarith

    -- Backward direction: If x = 1 and y = 1, then equality holds
    .
      intro h
      rcases h with ⟨h2, h3⟩
      subst x y
      ring_nf
