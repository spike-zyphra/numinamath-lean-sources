import Mathlib

theorem algebra_13164 (h : ℝ → ℝ) (h_def : h = fun t => -16 * t ^ 2 + 32 * t + 15) :
    IsGreatest (Set.image h {t | t ≥ 0}) 31 := by 
  have h_eq : ∀ t, h t = -16 * t ^ 2 + 32 * t + 15 := by 
    intro t 
    rw [h_def]
  constructor
  · -- Prove 31 is in the image of h for t >= 0
    use 1 
    constructor 
    · norm_num 
    · -- Show that h(1) = 31 
      rw [h_eq] 
      norm_num 
  · -- Prove that 31 is the greatest value in the image 
    intro y 
    rintro ⟨t, ht, rfl⟩ 
    have ht0 : t ≥ 0 := ht 
    have h_le : h t ≤ 31 := by 
      rw [h_eq] 
      nlinarith [sq_nonneg (t - 1)]
    linarith [h_le]