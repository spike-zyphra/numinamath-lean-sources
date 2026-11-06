import Mathlib

open Real

/- Let $a_{i}$ and $b_{i}$ be strictly positive real numbers. Show that $\sum \frac{a_{i}^{2}}{b_{i}} \geqslant \frac{\left(\sum a_{i}\right)^{2}}{\sum b_{i}}$.
-/
theorem inequalities_135810 (n : ℕ) (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∑ i, (a i)^2 / b i ≥ (∑ i, a i)^2 / ∑ i, b i := by
  -- just use titu's lemma version of cauchy scwharzz
  apply Finset.sq_sum_div_le_sum_sq_div
  . simpa