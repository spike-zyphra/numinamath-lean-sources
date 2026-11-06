import Mathlib

theorem algebra_319844 {f : ℝ → ℝ} (hf : ∀ x > 0, f x - 2 * x * f (1 / x) + 3 * x ^ 2 = 0) :
    IsLeast (Set.image f (Set.Ioi 0)) 3 := by

  have h1 : ∀ x > 0, f x = x ^ 2 + 2 / x := by
    intro x hx
    have eq1 := hf x hx
    have eq2 := hf (1 / x) (by positivity)
    field_simp [show x ≠ 0 from by linarith] at eq1 eq2 ⊢
    ring_nf at eq1 eq2 ⊢
    nlinarith [sq_nonneg (x - 1), sq_nonneg (f x - 3), sq_nonneg (f (1 / x) - 3), mul_pos hx (show (0 : ℝ) < x by linarith)]

  have h2 : 3 ∈ Set.image f (Set.Ioi 0) := by
    use 1
    constructor
    · norm_num
    · -- Show that $f(1) = 3$
      have h1_1 := h1 1 (by norm_num)
      norm_num at h1_1 ⊢
      linarith

  have h3 : ∀ y, y ∈ Set.image f (Set.Ioi 0) → 3 ≤ y := by
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx1 : 0 < x := by
      simpa using hx
    have eq1 := h1 x hx1
    have eq2 : f x = x ^ 2 + 2 / x := by
      simpa using eq1
    rw [eq2] at hfx
    have h4 : x ^ 2 + 2 / x ≥ 3 := by
      have h5 : x ^ 2 + 2 / x - 3 ≥ 0 := by
        have h6 : x ^ 2 + 2 / x - 3 = (x ^ 3 + 2 - 3 * x) / x := by
          field_simp
          <;> ring
        rw [h6] at *
        apply div_nonneg
        · -- Show numerator is non-negative
          have h7 : x ^ 3 + 2 - 3 * x ≥ 0 := by
            nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 2), mul_pos hx (show (0 : ℝ) < x by linarith), sq_nonneg (x ^ 2 - 1)]
          linarith
        · -- Show denominator is non-negative
          linarith
      linarith
    linarith [hfx, h4]

  constructor
  · exact h2
  · -- Show there is no smaller element
    intro y hy
    have := h3 y hy
    linarith