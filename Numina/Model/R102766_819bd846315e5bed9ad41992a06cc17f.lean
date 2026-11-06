import Mathlib

theorem algebra_313815 (a : ℝ) (ha : 0 < a ∧ a < 1)
    (f g : ℝ → ℝ)
    (hf : ∀ x, f x = a * x ^ 3 + (1 - 4 * a) * x ^ 2 + (5 * a - 1) * x + (3 - 5 * a))
    (hg : ∀ x, g x = (1 - a) * x ^ 3 - x ^ 2 + (2 - a) * x - (3 * a + 1)) :
    ∀ x, |f x| ≥ 1 + a ∨ |g x| ≥ 1 + a := by
  intro x
  by_contra h
  push_neg at h
  have h1 : |f x| < 1 + a := by linarith [h.1]
  have h2 : |g x| < 1 + a := by linarith [h.2]
  have h3 : -(1 + a) < f x := by
    linarith [abs_lt.mp h1]
  have h4 : f x < 1 + a := by
    linarith [abs_lt.mp h1]
  have h5 : -(1 + a) < g x := by
    linarith [abs_lt.mp h2]
  have h6 : g x < 1 + a := by
    linarith [abs_lt.mp h2]
  have hfx : f x = a * x ^ 3 + (1 - 4 * a) * x ^ 2 + (5 * a - 1) * x + (3 - 5 * a) := hf x
  have hgx : g x = (1 - a) * x ^ 3 - x ^ 2 + (2 - a) * x - (3 * a + 1) := hg x
  rw [hfx] at h3 h4
  rw [hgx] at h5 h6
  nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg (x - 1), 
    sq_nonneg (a - 1 / 2), sq_nonneg (a - 1 / 2), 
    ha.1, ha.2, 
    abs_lt.mp h1, abs_lt.mp h2
  ]