import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_66776 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
  (m M : ℝ) (hm : m ≤ M) (hx : ∀ i, x i ∈ Icc m M)
  (hsum : ∑ i, x i = 0) :
  ∑ i, (x i)^2 ≤ -n * m * M := by
  have h1 : ∀ i, m ≤ x i ∧ x i ≤ M := by
    intro i
    exact hx i
  -- for each $x_i$, we have $0 ≤ x_i -m ≤ M - m$, so $0 ≤ (x_i - m)(M - x_i)$
  have h2 : ∀ i, (x i - m) * (M - x i) ≥ 0 := by
    intro i
    have h11 : m ≤ x i := (h1 i).left
    have h12 : x i ≤ M := (h1 i).right
    nlinarith
  -- we have $x_i ^2 ≤ (M + m) * x_i - m * M$
  have h3 : ∀ i, (x i) ^ 2 ≤ (M + m) * (x i) - m * M := by
    intro i
    have h11 : m ≤ x i := (h1 i).left
    have h12 : x i ≤ M := (h1 i).right
    nlinarith [h2 i]
  have h4 : ∑ i, (x i) ^ 2 ≤ ∑ i, ((M + m) * (x i) - m * M) := by
    apply Finset.sum_le_sum
    intro i _
    exact h3 i
  have h5 : ∑ i, ((M + m) * (x i) - m * M) = (M + m) * (∑ i, (x i)) - n * (m * M) := by
    rw [Finset.sum_sub_distrib]
    congr
    . -- Show that ∑ i, (M + m) * (x i) = (M + m) * (∑ i, (x i))
      rw [←Finset.mul_sum]
    . -- Show that ∑ i, (m * M) = n * (m * M)
      simp [Finset.sum_const, Finset.card_univ, mul_comm]
      <;> ring
  rw [h5] at h4
  rw [hsum] at h4
  nlinarith