import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- 13.22. Points $A_{1}, \ldots, A_{n}$ lie on a circle with center $O$, and $\overrightarrow{O A_{1}}+\ldots+\overrightarrow{O A_{n}}=\overrightarrow{0}$. Prove that for any point $X$ the inequality $X A_{1}+\ldots+X A_{n} \geqslant n R$ holds, where $R$ is the radius of the circle. -/
theorem inequalities_109630 {n : ℕ} {R : ℝ} (hR : 0 < R) (hn : 0 < n) (A : Fin n → EuclideanSpace ℝ (Fin 2))
  (hA : ∀ i, dist 0 (A i) = R) (hA' : ∑ i, (A i) = 0) :
  ∀ X, ∑ i, dist X (A i) ≥ n * R := by
  rintro X
  -- multiply ‖A i‖ / R to each term in sum
  change n * R ≤ ∑ i, dist X (A i)
  convert_to n * R ≤ (∑ i, (‖(A i) - X‖ * ‖A i‖)) / R using 1
  . rw [Finset.sum_div]
    rw [sum_congr rfl]
    rintro i hi
    have := hA i
    simp at this
    rw [this]
    field_simp
    rw [← norm_neg]
    simp; rfl
  -- we'll show n * R = (∑ i : Fin n, inner (A i  - X) (A i)) / R, as this is true by using cauchy schwarze on each term
  suffices n * R = (∑ i : Fin n, inner (A i  - X) (A i)) / R by
    rw [this]
    gcongr
    exact real_inner_le_norm _ _
  calc
    -- now n * R = sum of R^2 / R over i
    n * R = (∑ i : Fin n, R^2) / R  := by simp; field_simp; ring
    -- which equals (A(i) ⬝ A(i)) for each term
    _ = (∑ i, inner (A i) (A i)) / R := by
      congr
      ext i
      rw [real_inner_self_eq_norm_sq]
      congr
      rw [← hA i]
      simp
    -- we can add sum of X ⬝ A(i) / R as X times sum of A(i) is 0
    _ = (∑ i, inner (A i) (A i)) / R - (∑ i, inner X (A i)) / R := by
      suffices ∑ i, inner X (A i) = (0:ℝ) by
        rw [this]; ring
      have : inner X (∑ i, A i) = ∑ i, (inner X (A i) : ℝ) := by
        exact inner_sum univ A X
      rw [← this]
      rw [hA']
      simp
    -- this finally makes the target true
    _ = (∑ i, inner (A i - X) (A i)) / R := by
      field_simp
      rw [← Finset.sum_sub_distrib]
      congr; ext i
      ring