import Mathlib

theorem algebra_203720 (weight : ℕ → ℝ) (h₀ : ∀ i ∈ Finset.range 50, weight i = weight 0 + 2 * i)
    (h₁ : weight 0 = 370) :
    ∑ i ∈ Finset.range 50, weight i ≤ 7 * 3 * 1000 := by 
  have eq1 : ∀ i ∈ Finset.range 50, weight i = 370 + 2 * ((i : ℝ)) := by
    intro i hi
    have h2 : weight i = weight 0 + 2 * i := h₀ i hi
    rw [h₁] at h2
    simpa using h2
  have h2 : ∑ i in Finset.range 50, weight i = 20950 := by 
    rw [Finset.sum_congr rfl (fun i hi => eq1 i hi)]
    norm_num [Finset.sum_range_succ]
  norm_num [h2]