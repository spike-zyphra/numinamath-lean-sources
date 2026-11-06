import Mathlib

theorem algebra_128920 (x : Fin 80 → ℝ) (h : ∑ i, (x i + 5)^2 = ∑ i, x i^2) :
    ∑ i, (x i + 6)^2 = ∑ i, x i^2 + 480 := by

  have h1 : ∑ i : Fin 80, (x i + 5) ^ 2 = ∑ i : Fin 80, x i ^ 2 := h

  have eq2 : ∑ i : Fin 80, (x i + 5) ^ 2 = ∑ i : Fin 80, (x i ^ 2 + 10 * x i + 25) := by
    apply Finset.sum_congr
    · rfl
    · intro i _
      ring_nf

  rw [eq2] at h1

  have eq3 : ∑ i : Fin 80, (x i ^ 2 + 10 * x i + 25) = ∑ i : Fin 80, x i ^ 2 + 10 * (∑ i : Fin 80, x i) + (25 * (80 : ℝ)) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
    <;> ring_nf

  rw [eq3] at h1

  have h2 : 10 * (∑ i : Fin 80, x i) + (25 * (80 : ℝ)) = 0 := by
    linarith

  have h3 : ∑ i : Fin 80, x i = -200 := by
    linarith

  have eq4 : ∑ i : Fin 80, (x i + 6) ^ 2 = ∑ i : Fin 80, (x i ^ 2 + 12 * x i + 36) := by
    apply Finset.sum_congr
    · rfl
    · intro i _
      ring_nf

  rw [eq4]

  have eq5 : ∑ i : Fin 80, (x i ^ 2 + 12 * x i + 36) = ∑ i : Fin 80, x i ^ 2 + 12 * (∑ i : Fin 80, x i) + (36 * (80 : ℝ)) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
    <;> ring_nf

  rw [eq5]

  rw [h3]

  linarith