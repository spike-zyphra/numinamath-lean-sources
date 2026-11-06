import Mathlib

theorem inequalities_597438 (a : Fin 59 → ℝ)
    (h₀ : ∀ i, a i ∈ Set.Icc (-2) 17)
    (h₁ : ∑ i, a i = 0) :
    ∑ i, (a i)^2 ≤ 2006 := by
  have h2 : ∀ i, -2 ≤ a i ∧ a i ≤ 17 := by
    intro i
    specialize h₀ i 
    simpa using h₀ 
  have h3 : ∀ i : Fin 59, (a i) ^ 2 ≤ 15 * (a i) + 34 := by 
    intro i
    have h4 : -2 ≤ a i ∧ a i ≤ 17 := h2 i 
    have h5 : -2 ≤ a i := h4.1 
    have h6 : a i ≤ 17 := h4.2 
    nlinarith [sq_nonneg (a i - 17), sq_nonneg (a i + 2)]
  have h4 : ∑ i, (a i) ^ 2 ≤ ∑ i, (15 * (a i) + 34) := by
    apply Finset.sum_le_sum 
    intro i _ 
    specialize h3 i
    linarith
  have h5 : ∑ i, (15 * (a i) + 34) = 15 * (∑ i, (a i)) + 59 * 34 := by 
    simp [Finset.sum_add_distrib, Finset.mul_sum]
    <;> ring
  have h6 : ∑ i, (15 * (a i) + 34) = 2006 := by 
    rw [h5]
    rw [h₁]
    all_goals norm_num
  linarith [h4, h6]