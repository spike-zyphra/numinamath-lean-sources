import Mathlib

theorem algebra_179077 (x : Fin 100 → ℝ) (h : ∑ i : Fin 100, (x i + 1)^2 = ∑ i : Fin 100, x i^2) :
    ∃ y : ℝ, ∑ i : Fin 100, (x i + 2)^2 = ∑ i : Fin 100, x i^2 + y ∧ y = 200 := by
  have eqn1 : ∑ i : Fin 100, (x i + 1)^2 = ∑ i : Fin 100, x i^2 + 2 * (∑ i : Fin 100, x i) + 100 := by
    have h1 : ∑ i : Fin 100, (x i + 1)^2 = ∑ i : Fin 100, (x i ^ 2 + 2 * x i + 1 : ℝ) := by
      congr
      funext i
      ring
    rw [h1]
    simp [Finset.sum_add_distrib, Finset.mul_sum]
    <;> ring_nf <;> norm_num
    all_goals ring
  have h1 : 2 * (∑ i : Fin 100, x i) + 100 = 0 := by
    linarith [h, eqn1]
  have h2 : ∑ i : Fin 100, x i = -50 := by
    linarith
  use 200
  constructor
  · -- Show that the sum of squares changes by 200
    have eqn2 : ∑ i : Fin 100, (x i + 2)^2 = ∑ i : Fin 100, x i^2 + 4 * (∑ i : Fin 100, x i) + 400 := by
      have h1 : ∑ i : Fin 100, (x i + 2)^2 = ∑ i : Fin 100, (x i ^ 2 + 4 * x i + 4 : ℝ) := by
        congr
        funext i
        ring
      rw [h1]
      simp [Finset.sum_add_distrib, Finset.mul_sum]
      <;> ring_nf <;> norm_num
      all_goals ring
    rw [eqn2]
    rw [h2]
    all_goals linarith
  · -- Show that y = 200
    rfl