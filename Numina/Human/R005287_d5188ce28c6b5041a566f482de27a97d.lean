import Mathlib

/- Soient $a_{1}, \ldots, a_{101}$ des réels appartenant à l'intervalle $[-2 ; 10]$ tels que

$$
a_{1}+\ldots+a_{101}=0
$$

Montrer que

$$
a_{1}^{2}+\ldots+a_{101}^{2} \leqslant 2020
$$ -/
theorem inequalities_607414 (a : Fin 101 → ℝ) (ha : ∀ i, a i ∈ Set.Icc (-2) 10) (hsum : ∑ i, a i = 0) : ∑ i, (a i)^2 ≤ 2020 := by
  have h1 : ∀ i, (a i) ^ 2 ≤ 8 * (a i) + 20 := by
    intro i
    have h2 : -2 ≤ a i ∧ a i ≤ 10 := by 
      simpa using ha i
    nlinarith [sq_nonneg (a i - 10), sq_nonneg (a i + 2)]
  have h2 : ∑ i, (a i) ^ 2 ≤ ∑ i, (8 * (a i) + 20) := by
    apply Finset.sum_le_sum
    intro i hi
    have h3 : (a i) ^ 2 ≤ 8 * (a i) + 20 := h1 i
    linarith
  have h3 : ∑ i, (8 * (a i) + 20) = 8 * (∑ i, (a i)) + 101 * 20 := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  rw [h3] at h2
  rw [hsum] at h2
  norm_num at h2 ⊢
  linarith