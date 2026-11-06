import Mathlib

theorem inequalities_66428 (a : Fin 59 → ℝ)
    (h₁ : ∀ i, a i ∈ Set.Icc (-2) 17)
    (h₂ : ∑ i, a i = 0) :
    ∑ i, (a i)^2 ≤ 2006 := by
  have h3 : ∀ i, -2 ≤ a i ∧ a i ≤ 17 := by 
    intro i
    have h3i : a i ∈ Set.Icc (-2) 17 := h₁ i
    exact h3i
  -- Show that for each i, a_i ^2 ≤ 15 * a_i + 34
  have h4 : ∀ i : Fin 59, (a i) ^ 2 ≤ 15 * (a i) + 34 := by
    intro i
    have h5 : -2 ≤ a i := (h3 i).left
    have h6 : a i ≤ 17 := (h3 i).right
    nlinarith [sq_nonneg ((a i) - 17), sq_nonneg ((a i) + 2), h5, h6]

  have h5 : ∑ i : Fin 59, (a i) ^ 2 ≤ ∑ i : Fin 59, (15 * (a i) + 34) := by
    apply Finset.sum_le_sum 
    intro i hi
    exact h4 i 

  have h6 : ∑ i : Fin 59, (15 * (a i) + 34) = 2006 := by
    calc 
      ∑ i : Fin 59, (15 * (a i) + 34) = 15 * (∑ i, (a i)) + 59 * 34 := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
        all_goals ring
      _ = 15 * (0) + 59 * 34 := by
        rw [h₂]
      _ = 2006 := by
        norm_num
  
  linarith [h5, h6]