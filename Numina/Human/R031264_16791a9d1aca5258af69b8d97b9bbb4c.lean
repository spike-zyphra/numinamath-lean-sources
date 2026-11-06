import Mathlib
/- Let $a, b, c$ be real numbers such that $a^{2}+b^{2}+c^{2}=1$. Prove that. $P=a b+b c+c a-2(a+b+c) \geq-\frac{5}{2}$. Are there values of $a, b, c$, such that $P=-\frac{5}{2}$. -/
theorem algebra_606026 : (∀ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 = 1 → a * b + b * c + c * a - 2 * (a + b + c) ≥ -5 / 2) ∧ ¬(∃ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 = 1 ∧ a * b + b * c + c * a - 2 * (a + b + c) = -5 / 2) := by
  constructor
  . -- Part 1: Prove P ≥ -5/2
    intro a b c h
    -- Express sum of products in terms of squared sum and sum of squares
    have h1 : a * b + b * c + c * a = ((a + b + c) ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2)) / 2:= by ring
    rw [h] at h1
    -- Let t = a + b + c for simpler notation
    set t:= a + b + c with ht
    clear_value t
    rw [h1]
    -- Use the fact that (t-2)² ≥ 0 for any real t
    have h2 : (t - 2) ^ 2 ≥ 0:= by positivity
    linarith
  . -- Part 2: Prove P = -5/2 is impossible
    by_contra H
    rcases H with ⟨a, b, c, h2, h3⟩
    -- Use the same algebraic identity as in Part 1
    have h1 : a * b + b * c + c * a = ((a + b + c) ^ 2 - (a ^ 2 + b ^ 2 + c ^ 2)) / 2:= by ring
    rw [h1, h2] at h3
    set t:= a + b + c with ht
    clear_value t
    -- If P = -5/2, then (t-2)² = 0
    replace h3 : (t - 2) ^ 2 = 0:= by linarith
    -- Therefore t-2 = 0
    replace h3 : t - 2 = 0:= by exact pow_eq_zero h3
    -- Use the inequality: 3(a² + b² + c²) - (a + b + c)² ≥ 0
    -- This comes from sum of squared differences being non-negative
    have h4 : 3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2 ≥ 0:= by
      have g1 : (a - b) ^ 2 ≥ 0:= by positivity
      have g2 : (b - c) ^ 2 ≥ 0:= by positivity
      have g3 : (c - a) ^ 2 ≥ 0:= by positivity
      linarith
    rw [h2, ←ht] at h4
    replace h3 : t = 2:= by linarith
    rw [h3] at h4
    -- This leads to a contradiction
    linarith
