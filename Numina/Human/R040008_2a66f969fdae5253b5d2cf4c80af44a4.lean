import Mathlib

/-
Problem 2. Prove that if $a, b$ and $c$ are positive numbers with sum 3 , then

$$
\frac{a}{b^{2}+1}+\frac{b}{c^{2}+1}+\frac{c}{a^{2}+1} \geq \frac{3}{2}
$$

Mediteranian Mathematical Competition
-/
theorem inequalities_295992 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 3) :
    3 / 2 ≤ a / (b ^ 2 + 1) + b / (c ^ 2 + 1) + c / (a ^ 2 + 1) := by
  
  -- A auxilarie to prove the inequality using non-negativity of square differences.
  have h1 : ∀ x y : ℝ, x > 0 → y > 0 → x / (y ^ 2 + 1) - (x - x * y / 2) ≥ 0 := by
    intro x y hx hy
    have h1 : x / (y ^ 2 + 1) - (x - x * y / 2) = x * y * (y - 1) ^ 2 / (2 * (y ^ 2 + 1)) := by
      field_simp
      ring
    rw [h1]
    positivity
  
  -- Apply the auxiliary lemma for all pairs of variables
  have h2 := h1 a b ha hb
  have h3 := h1 b c hb hc
  have h4 := h1 c a hc ha
  
  -- Let the prover finish the proof using linarith tactic which uses linear arithmetic reasoning.
  have h5 : a / (b ^ 2 + 1) + b / (c ^ 2 + 1) + c / (a ^ 2 + 1) - 3 / 2 ≥ 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
              sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              h2, h3, h4, hsum, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  linarith