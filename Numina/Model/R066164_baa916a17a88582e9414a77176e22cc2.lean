import Mathlib

theorem algebra_128222 (n : ℕ) (hn : 0 < n) (a x : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i)
    (a_sum : ℝ) (c_sum : ℝ)
    (h_a_sum : a_sum = ∑ i, a i)
    (h_c_sum : c_sum = ∑ i, a i * x i) :
    0 ≤ a_sum ∧ 0 ≤ c_sum := by
  have h1 : 0 ≤ a_sum := by
    rw [h_a_sum]
    apply Finset.sum_nonneg
    intro i hi
    exact ha i
  have h2 : 0 ≤ c_sum := by
    rw [h_c_sum]
    apply Finset.sum_nonneg
    intro i hi
    have ha1 : 0 ≤ a i := ha i
    have hx1 : 0 ≤ x i := hx i
    exact mul_nonneg ha1 hx1
  constructor
  · exact h1
  · exact h2