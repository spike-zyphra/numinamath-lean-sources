import Mathlib

theorem algebra_93664 (s : ℝ → ℝ) (h₀ : ∀ t, s t = 160 * t - 16 * t ^ 2) :
    IsGreatest (Set.image s {t | t ≥ 0}) 400 := by
  have h1 : ∀ t, s t = 160 * t - 16 * t ^ 2 := h₀
  constructor
  · -- Show 400 is in the image
    use 5
    constructor
    · -- Show 5 ≥ 0
      norm_num
    · -- Show s 5 = 400
      rw [h1 5]
      norm_num
  · -- Show 400 is greatest in the image
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    have ht_nonneg : t ≥ 0 := ht
    have h2 : s t ≤ 400 := by
      rw [h1 t]
      nlinarith [sq_nonneg (t - 5)]
    linarith