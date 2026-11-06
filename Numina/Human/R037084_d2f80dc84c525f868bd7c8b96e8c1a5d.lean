import Mathlib
/-Let $a$ be a real number. To ensure that for any $x\in \left( -\infty ,1 \right)\cup \left( 5,+\infty \right)$, we have ${{x}^{2}}-2\left( a-2 \right)x+a>0$, the set of all $a$ that satisfy the above requirement is ( )

A:$\left( -\infty ,5 \right]$
B:$\left( 1,4 \right)$
C:$\left( 1,7 \right]$
D:$\left( 1,5 \right]$-/
theorem algebra_12297 (a : ℝ) :
    (∀ x : ℝ, (x < 1 ∨ x > 5) → x^2 - 2 * (a - 2) * x + a > 0) ↔
    1 < a ∧ a ≤ 5 := by
  constructor
  · -- Assume the inequality holds for all x in (-∞,1)∪(5,+∞)
    intro h
    have h1 := h (-1) (Or.inl (by norm_num))
    have h2 := h 6 (Or.inr (by norm_num))
    have h3 : a > 1 := by nlinarith
    have h4 : a ≤ 5 := by
      by_contra h'
      push_neg at h'
      have h5 := h (5 + (a - 5) / 8) (Or.inr (by linarith))
      nlinarith [sq_nonneg (a - 5 + (a - 5) / 8), sq_nonneg (a - 5), sq_nonneg (a - 5 + (a - 5) / 8 - 5)]
    exact ⟨h3, h4⟩
  · -- Assume 1 < a ≤ 5, prove the inequality holds for all x ∈ (-∞,1)∪(5,+∞)
    rintro ⟨ha1, ha2⟩
    intro x hxy
    rcases hxy with h1 | h2
    · -- Case x < 1
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 5), sq_nonneg (x - (a - 2)), sq_nonneg (a - 2), sq_nonneg (a - 3), sq_nonneg (a - 4), sq_nonneg (a - 1), sq_nonneg (x - 1 + a - 2), sq_nonneg (x - 5 - a + 2)]
    · -- Case x > 5
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 5), sq_nonneg (x - (a - 2)), sq_nonneg (a - 2), sq_nonneg (a - 3), sq_nonneg (a - 4), sq_nonneg (a - 1), sq_nonneg (x - 1 - a + 2), sq_nonneg (x - 5 + a - 2)]