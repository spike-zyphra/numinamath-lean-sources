import Mathlib

theorem inequalities_230499 (n : ℕ) :
    (∀ x y z : ℝ, (x^2 + y^2 + z^2)^2 ≤ n * (x^4 + y^4 + z^4)) ↔ n ≥ 3 := by
  constructor
  · -- Forward direction: ∀ x y z, (x^2 + y^2 + z^2)^2 ≤ n * (x^4 + y^4 + z^4) → n ≥ 3.
    intro h
    have h111 := h 1 1 1
    norm_num at h111
    have : (n : ℝ) ≥ 3 := by nlinarith
    exact_mod_cast this
  · -- Backward direction: n ≥ 3 → ∀ x y z, (x^2 + y^2 + z^2)^2 ≤ n * (x^4 + y^4 + z^4).
    intro hn
    intro x y z
    have h1 : (x^2 + y^2 + z^2) ^ 2 ≤ 3 * (x^4 + y^4 + z^4) := by
      linarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2)]
    have hn' : (n : ℝ) ≥ 3 := by exact_mod_cast hn
    have h2 : (x^2 + y^2 + z^2) ^ 2 ≤ (n : ℝ) * (x^4 + y^4 + z^4) := by
      nlinarith [h1]
    exact_mod_cast h2