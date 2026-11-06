import Mathlib

theorem number_theory_114610 (h:100^10 = ∑ i ∈ Finset.range n, 10) : n = 10^19 := by
  have h1 : ∑ i in Finset.range n, 10 = 10 * n := by
    simp [Finset.sum_const, Finset.card_range, mul_comm]
    <;> ring

  rw [h1] at h
  have h2 : 100 ^ 10 = 10 * (n : ℕ) := h

  have h3 : n = 10 ^ 19 := by
    omega

  exact h3