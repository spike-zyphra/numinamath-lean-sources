import Mathlib

open Real
open scoped BigOperators

theorem inequalities_4535 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc 0 2) (hxs : ∑ i, x i = n) :
    ∑ i, (x i + 1) * (5 - 3 * x i) > 0 := by
  have h1 : ∀ i, 0 ≤ x i ∧ x i ≤ 2 := by
    intro i
    specialize hx i
    simpa using hx

  have h2 : ∑ i : Fin n, (x i + 1) * (5 - 3 * x i) = 7 * (n : ℝ) - 3 * (∑ i : Fin n, (x i) ^ 2) := by
    have h3 : ∀ i : Fin n, (x i + 1) * (5 - 3 * x i) = -3 * (x i) ^ 2 + 2 * (x i) + 5 := by
      intro i
      ring
    have h4 : ∑ i : Fin n, (x i + 1) * (5 - 3 * x i) = ∑ i : Fin n, (-3 * (x i) ^ 2 + 2 * (x i) + 5) := by
      apply Finset.sum_congr
      . rfl
      intro i hi
      specialize h3 i
      linarith
    rw [h4]
    have h5 : ∑ i : Fin n, (-3 * (x i) ^ 2 + 2 * (x i) + 5) = -3 * (∑ i : Fin n, (x i) ^ 2) + 2 * (∑ i : Fin n, (x i)) + 5 * n := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
      <;> ring
    rw [h5, hxs]
    all_goals ring

  have h3 : ∑ i : Fin n, (x i) ^ 2 ≤ 2 * (n : ℝ) := by
    have h4 : ∀ i : Fin n, (x i) ^ 2 ≤ 2 * (x i) := by
      intro i
      have h11 := h1 i
      have h111 : 0 ≤ x i := h11.1
      have h112 : x i ≤ 2 := h11.2
      nlinarith [sq_nonneg (x i - 2)]
    have h5 : ∑ i : Fin n, (x i) ^ 2 ≤ 2 * (∑ i : Fin n, (x i)) := by
      calc
        ∑ i : Fin n, (x i) ^ 2 = ∑ i : Fin n, ((x i) ^ 2) := by rfl
        _ ≤ ∑ i : Fin n, (2 * (x i)) := by
          apply Finset.sum_le_sum
          intro i hi
          specialize h4 i
          linarith
        _ = 2 * (∑ i : Fin n, (x i)) := by
          simp [Finset.mul_sum]
    rw [hxs] at h5
    linarith

  rw [h2]

  have h33 : ∑ i : Fin n, (x i) ^ 2 ≤ 2 * (n : ℝ) := h3
  have hn1 : (n : ℝ) > 0 := by exact_mod_cast (show (0 : ℕ) < n by linarith)

  nlinarith [h33, hn1]