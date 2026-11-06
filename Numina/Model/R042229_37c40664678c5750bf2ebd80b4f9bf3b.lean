import Mathlib

theorem algebra_13849 (x : Fin 100 → ℝ) (hsum : ∑ i, x i = 1) (h_ne_one: ∀ i, x i ≠ 1)
    (hfraction : ∑ i, x i / (1 - x i) = 1) :
    ∑ i, (x i) ^ 2 / (1 - x i) = 0 := by
  have h1 : ∀ i, (x i) ^ 2 / (1 - x i) = (x i / (1 - x i)) - x i := by 
    intro i 
    have hx : x i ≠ 1 := h_ne_one i 
    field_simp [(show (1 - x i) ≠ 0 by intro h; apply hx; linarith)]
    <;> ring
  have h2 : ∑ i, (x i) ^ 2 / (1 - x i) = ∑ i, ( (x i / (1 - x i)) - x i ) := by 
    apply Finset.sum_congr 
    · rfl 
    · intro i _ 
      exact h1 i
  rw [h2]
  have h3 : ∑ i, ( (x i / (1 - x i)) - x i ) = (∑ i, (x i / (1 - x i))) - (∑ i, x i ) := by 
    simp [Finset.sum_sub_distrib]
    <;> ring 
  rw [h3]
  rw [hfraction, hsum]
  all_goals norm_num 
  all_goals linarith