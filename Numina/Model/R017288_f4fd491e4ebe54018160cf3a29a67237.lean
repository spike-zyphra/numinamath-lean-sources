import Mathlib

theorem inequalities_294046 (a : Fin 101 → ℝ)
    (h₀ : ∀ i, a i ∈ Set.Icc (-2) 10)
    (h₁ : ∑ i, a i = 0) :
    ∑ i, (a i)^2 ≤ 2020 := by 
  have h2 : ∀ i, -2 ≤ a i ∧ a i ≤ 10 := by
    intro i
    specialize h₀ i
    simpa using h₀
  have h3 : ∀ i, (a i) ^ 2 ≤ 8 * (a i) + 20 := by
    intro i
    have h4 : -2 ≤ a i := (h2 i).1
    have h5 : a i ≤ 10 := (h2 i).2
    nlinarith [sq_nonneg (a i + 2), sq_nonneg (a i - 10), mul_nonneg (show 0 ≤ 10 - a i by linarith) (show 0 ≤ a i + 2 by linarith), sq_nonneg (a i - 4)]
  have h4 : ∑ i, (a i ^ 2) ≤ ∑ i, (8 * (a i) + 20) := by
    apply Finset.sum_le_sum
    intro i hi
    specialize h3 i
    linarith 
  have h5 : ∑ i, (8 * (a i) + 20) = 8 * (∑ i, (a i)) + 101 * 20 := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
    <;> ring
  rw [h5] at h4
  rw [h₁] at h4
  norm_num at h4 ⊢ 
  linarith [h4]