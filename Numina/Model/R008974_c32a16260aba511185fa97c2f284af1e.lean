import Mathlib

theorem algebra_10400 (h : ℝ → ℝ) (h_def : h = fun t => -16 * t ^ 2 + 80 * t + 21) :
    IsGreatest (Set.image h (Set.Ici 0)) 121 := by
  have h1 : ∀ t, h t = -16 * t^2 + 80 * t + 21 := by 
    intro t
    rw [h_def]
  constructor
  · -- Show that 121 is in the image of h over [0, ∞)
    use 2.5
    constructor
    · -- Show that 2.5 ≥ 0 
      norm_num
    · -- Show that h(2.5) = 121 
      rw [h1]
      norm_num
  · -- Show that for any value in the image of h over [0, ∞), it ≤ 121
    intro y
    rintro ⟨t, ht, rfl⟩
    have hht : h t = -16 * t^2 + 80 * t + 21 := h1 t
    rw [hht]
    have ht0 : 0 ≤ t := ht
    nlinarith [sq_nonneg (t - 2.5)]