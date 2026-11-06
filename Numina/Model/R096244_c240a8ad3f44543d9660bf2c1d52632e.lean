import Mathlib

def f (x y : ℝ) := x * (1 - y)

theorem algebra_240151 (a : ℝ) :
    (∀ x : ℝ, f (x - a) (x + a) < 1) ↔ -1 / 2 < a ∧ a < 3 / 2 := by
  constructor
  · -- Forward direction: If $(x - a) \otimes (x + a) < 1$ for all $x \in \mathbb{R}$, then $-\frac{1}{2} < a < \frac{3}{2}$
    intro h
    have h₁ := h (1 / 2)
    simp [f] at h₁
    constructor
    · -- Prove -1 / 2 < a
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2), sq_nonneg (a - 3 / 2)]
    · -- Prove a < 3 / 2
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2), sq_nonneg (a - 3 / 2)]
  · -- Backward direction: If $-\frac{1}{2} < a < \frac{3}{2}$, then $(x - a) \otimes (x + a) < 1$ for all $x \in \mathbb{R}$
    rintro ⟨h₁, h₂⟩
    intro x
    simp [f]
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2), sq_nonneg (a - 3 / 2)]