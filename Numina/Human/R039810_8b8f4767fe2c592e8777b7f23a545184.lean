import Mathlib
/- Find all real values of $x$ for which

$$
\frac{1}{\sqrt{x}+\sqrt{x-2}}+\frac{1}{\sqrt{x+2}+\sqrt{x}}=\frac{1}{4}
$$ -/
theorem algebra_608897 (x : ℝ) (hx : x ≥ 2) : 1 / (√x + √(x - 2)) + 1 / (√x + √(x + 2)) = 1 / 4 ↔ x = 257 / 16:= by

  -- Helper lemma h1: proves the function is strictly decreasing
  -- For any x, y ≥ 2, if x > y, then f(x) < f(y)
  have h1 : ∀ x y : ℝ, x ≥ 2 → y ≥ 2 → x > y → 1 / (√x + √(x - 2)) + 1 / (√x + √(x + 2)) < 1 / (√y + √(y - 2)) + 1 / (√y + √(y + 2)):= by
    intro x y _ hy hxy
    -- Prove that square roots preserve ordering
    have h1 : √x > √y:= by exact Real.sqrt_lt_sqrt (by linarith) hxy
    have h2 : √(x - 2) > √(y - 2):= by exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have h3 : √(x + 2) > √(y + 2):= by exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
    replace h2 : √x + √(x - 2) > √y + √(y - 2):= by linarith
    replace h3 : √x + √(x + 2) > √y + √(y + 2):= by linarith
    -- Apply reciprocal inequality (larger denominator means smaller fraction)
    replace h2 : 1 / (√x + √(x - 2)) < 1 / (√y + √(y - 2)):= by exact one_div_lt_one_div_of_lt (by positivity) h2
    replace h3 : 1 / (√x + √(x + 2)) < 1 / (√y + √(y + 2)):= by exact one_div_lt_one_div_of_lt (by positivity) h3
    linarith

  -- Helper lemma h2: proves that x = 257/16 is indeed a solution
  have h2 : ∀ x : ℝ, x = 257 / 16 → 1 / (√x + √(x - 2)) + 1 / (√x + √(x + 2)) = 1 / 4:= by
    intro x hx
    -- Simplify fractions using algebraic identities
    rw [show 1 / (√x + √(x - 2)) = (√x - √(x - 2)) / 2 by field_simp ; ring_nf ; rw [Real.sq_sqrt (by linarith)] ; rw [Real.sq_sqrt (by linarith)] ; ring_nf]
    rw [show 1 / (√x + √(x + 2)) = (√(x + 2) - √x) / 2 by field_simp ; ring_nf ; rw [Real.sq_sqrt (by linarith)] ; rw [Real.sq_sqrt (by linarith)] ; ring_nf]
    ring_nf
    subst x
    ring_nf
    -- Simplify numerical expressions
    rw [show (225 : ℝ) / 16 = (15 / 4) ^ 2 by norm_num]
    rw [show (289 : ℝ) / 16 = (17 / 4) ^ 2 by norm_num]
    field_simp
    linarith

  -- Prove both directions of the if and only if statement
  constructor
  -- Forward direction: if equation holds, then x = 257/16
  .
    intro h
    specialize h2 (257 / 16) (by norm_num)
    by_contra H
    -- If x ≠ 257/16, then x must be either less or greater
    replace H : x < 257 / 16 ∨ x > 257 / 16:= by exact lt_or_gt_of_ne H
    rcases H with H | H
    -- Use monotonicity to reach contradiction in both cases
    .
      specialize h1 (257 / 16) x (by linarith) (by linarith) (by linarith)
      linarith
    .
      specialize h1 x (257 / 16) (by linarith) (by linarith) (by linarith)
      linarith
  -- Reverse direction: if x = 257/16, then equation holds
  .
    intro h
    specialize h2 x h
    exact h2
