import Mathlib

open Real

/- Let $n$ be a natural number. For any real numbers $x$, $y$, $z$, the inequality $\left( {{x}^{2}}+{{y}^{2}}+{{z}^{2}} \right)^2 \leqslant n\left( {{x}^{4}}+{{y}^{4}}+{{z}^{4}} \right)$ always holds, then the minimum value of $n$ is ___          ___. -/
theorem inequalities_9879 (n : ℕ) :
    (∀ x y z : ℝ, (x^2 + y^2 + z^2)^2 ≤ n * (x^4 + y^4 + z^4)) ↔ n ≥ 3 := by
  constructor
  · -- Forward direction: if the inequality holds, then n ≥ 3
    intro h
    have h111 := h 1 1 1
    norm_num at h111 
    have hn : (n : ℝ) ≥ 3 := by
      linarith
    have hn' : n ≥ 3 := by
      exact_mod_cast hn
    exact hn'
  · -- Backward direction: n ≥ 3 implies the inequality holds
    intro hn x y z
    have h1 : (x^2 + y^2 + z^2) ^ 2 ≤ 3 * (x^4 + y^4 + z^4) := by
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2)]
    have h2 : (3 : ℝ) ≤ n := by
      have h3 : (n : ℝ) ≥ 3 := by
        exact_mod_cast hn
      linarith
    have h3 : (x^2 + y^2 + z^2) ^ 2 ≤ (n : ℝ) * (x^4 + y^4 + z^4) := by
      have h4 : (n : ℝ) * (x^4 + y^4 + z^4) ≥ 3 * (x^4 + y^4 + z^4) := by
        nlinarith
      linarith [h1, h4]
    exact h3