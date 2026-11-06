import Mathlib

open Real

theorem algebra_598218 {t : ℝ} (ht : t > 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = 1 / (1 + x) - 1 / (1 + x) ^ 2 * (t - x)) :
    IsGreatest (Set.image f (Set.Ioi 0)) (f t) := by
  constructor
  · -- Show that f(t) is in the image of f over (0, +∞)
    use t
    constructor
    · -- Show that t > 0
      exact ht
    · -- Show that f(t) = f(t) (trivial)
      rfl
  · -- Show that f(t) is the greatest element in the image
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx1 : x > 0 := by
      simpa using hx
    have h1 : f x = 1 / (1 + x) - 1 / (1 + x) ^ 2 * (t - x) := hf x
    have h2 : f t = 1 / (1 + t) - 1 / (1 + t) ^ 2 * (t - t) := hf t
    have h3 : f t = 1 / (1 + t) := by
      rw [h2]
      field_simp
      all_goals linarith
    have h4 : f x ≤ f t := by
      rw [h1, h3]
      have h5 : 1 / (1 + x) - 1 / (1 + x) ^ 2 * (t - x) ≤ 1 / (1 + t) := by
        have h6 : 0 < (1 + x) := by
          linarith
        have h7 : 0 < (1 + x) ^ 2 := by
          positivity
        have h8 : 0 < (1 + t) := by
          nlinarith
        have h9 : (1 / (1 + x) - 1 / (1 + x) ^ 2 * (t - x) ) - 1 / (1 + t) ≤ 0 := by
          have h10 : ( (1 / (1 + x) - 1 / (1 + x) ^ 2 * (t - x) ) - 1 / (1 + t) ) =
              ( (1 + 2 * x - t ) * (1 + t) - (1 + x )^2 ) / ( (1 + x )^2 * (1 + t ) ) := by
            field_simp
            <;> ring
          rw [h10]
          apply div_nonpos_of_nonpos_of_nonneg
          · -- Numerator ≤ 0
            nlinarith [sq_nonneg (x - t)]
          · -- Denominator ≥ 0
            positivity
        linarith
      linarith
    have h5 : f x ≤ f t := h4
    linarith [hfx, h5]