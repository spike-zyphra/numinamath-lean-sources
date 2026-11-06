import Mathlib

theorem algebra_265546 (f : ℝ → ℝ) (hf : f = fun x => (3 * x ^ 2 + 3 * x + 4) / (x ^ 2 + x + 1)) :
    IsGreatest (Set.range f) (4 + 1 / 3) := by
  have h1 : ∀ x, f x = (3 * x ^ 2 + 3 * x + 4) / (x ^ 2 + x + 1) := by
    intro x
    rw [hf]

  have h2 : 4 + 1 / 3 ∈ Set.range f := by
    use (-1 / 2)
    rw [h1]
    norm_num

  have h3 : ∀ y, y ∈ Set.range f → y ≤ 4 + 1 / 3 := by
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1] at hx
    have h4 : (3 * x ^ 2 + 3 * x + 4) / (x ^ 2 + x + 1) ≤ 4 + 1 / 3 := by
      have h5 : x ^ 2 + x + 1 > 0 := by
        nlinarith [sq_nonneg (x + 1 / 2)]
      have h6 : 3 * (3 * x ^ 2 + 3 * x + 4) ≤ 13 * (x ^ 2 + x + 1) := by
        nlinarith [sq_nonneg (2 * x + 1)]
      have h7 : (3 * x ^ 2 + 3 * x + 4) / (x ^ 2 + x + 1) ≤ 4 + 1 / 3 := by
        have h8 : (x ^ 2 + x + 1) > 0 := h5
        apply (div_le_iff₀ h8).mpr
        nlinarith [h6]
      linarith [h7]
    linarith [h4, hx]

  exact ⟨h2, h3⟩