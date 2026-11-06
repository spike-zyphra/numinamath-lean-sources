import Mathlib

theorem algebra_192522 {f : ℝ → ℝ} (hf : ∀ x, 0 < x → f x - 2 * x * f (1 / x) + 3 * x ^ 2 = 0) :
    IsLeast (Set.image f (Set.Ioi 0)) 3 := by

  have h1 : ∀ x, 0 < x → f x = x ^ 2 + 2 / x := by
    intro x hx
    have eq1 := hf x hx
    have eq2 := hf (1 / x) (by positivity)
    have h2 : f (1 / x) - 2 * (1 / x) * f x + 3 * (1 / x) ^ 2 = 0 := by
      simpa using eq2

    field_simp [show x ≠ 0 by linarith] at eq1 h2 ⊢
    nlinarith [sq_nonneg (x - 1), sq_nonneg (f x - (x ^ 2 + 2 / x)), sq_pos_of_pos hx, sq_pos_of_pos (show (0 : ℝ) < 1 / x by positivity)]

  constructor
  · -- 3 is in the image
    use 1
    constructor
    · -- Show 1 is in (0, ∞)
      norm_num
    · -- Compute f(1)
      have h3 := h1 1 (by norm_num)
      norm_num at h3 ⊢
      linarith

  · -- Show no value less than 3 is in the image
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩

    have hx_pos : 0 < x := by
      simpa using hx

    have h4 : f x = x ^ 2 + 2 / x := h1 x hx_pos
    rw [h4] at hfx

    have h5 : x ^ 2 + 2 / x ≥ 3 := by
      have h6 : x ^ 2 + 2 / x - 3 ≥ 0 := by
        have h7 : x ^ 2 + 2 / x - 3 = (x ^ 3 - 3 * x + 2) / x := by
          field_simp
          ring
        rw [h7]
        have h8 : x ^ 3 - 3 * x + 2 ≥ 0 := by
          have h10 : x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2) := by
            ring
          rw [h10]
          have h11 : (x - 1) ^ 2 ≥ 0 := by
            apply sq_nonneg
          have h12 : x + 2 > 0 := by
            linarith
          nlinarith [sq_nonneg ((x - 1) ^ 2), sq_pos_of_pos (show (x + 2 : ℝ) > 0 by linarith), sq_nonneg ((x - 1) * (x + 2))]
        have h9 : x > 0 := by
          simpa using hx_pos
        apply div_nonneg
        linarith
        all_goals linarith
      linarith

    linarith