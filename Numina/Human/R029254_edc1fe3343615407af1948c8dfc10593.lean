import Mathlib
/-Find the positive base $b$ in which the equation $4 \cdot 12 = 103$ is valid. -/

theorem number_theory_19060 {b : ℕ} (hb : b > 0) (hb2 : b > 4): (4: ℝ ) *(1 * b + 2) = (1* b^2 + 0 * b + 3) ↔ b = 5 := by
  --When we rewrite the base numbers as sums of digit bundles, we get the equation $$ 4 \cdot (b + 2) = b^2 + 3 \ \ \Rightarrow \ \ b^2 - 4b - 5 = 0. $$Solving this quadratic equation, we get $b = 5$ and $b = -1$.  But, since the base must be positive, $b = \boxed{5}$.
  constructor
  .
    intro h
    ring_nf at h
    have e := congrArg ( fun (n) => ((n) - (8 : ℝ )- (↑b * 4 ))) h; simp at e
    symm at e
    rw [show (3 : ℝ ) + ↑b ^ 2 - 8 - ↑b * 4 = 1 * ↑b * ↑b  +(- 4) * ↑b +(-5) by ring_nf] at e
    have hd : discrim (1 : ℝ ) (-4) (-5) = discrim (1 : ℝ ) (-4) (-5) := by rfl
    have ha :  (1 : ℝ ) ≠ 0 := by linarith
    nth_rewrite 2[discrim] at hd; ring_nf at hd
    rw [show (36 : ℝ ) = 6 * 6 by ring_nf] at hd
    have heq := quadratic_eq_zero_iff  ha hd
    rw [mul_assoc, heq] at e
    simp at e; ring_nf at e
    cases e with
    | inl h =>
      norm_cast at h
    | inr h =>
      linarith
  .
    intro h
    rw [h]
    ring_nf
