import Mathlib

theorem algebra_276567 {f : ℝ → ℝ} (h1 : ∀ x, f (x ^ 3) = (f x) ^ 3) (h2 : ∀ x1 x2, x1 ≠ x2 → f x1 ≠ f x2) :
    f 0 + f 1 + f (-1) = 0 := by

  have h3 : f 0 = (f 0) ^ 3 := by
    specialize h1 0
    norm_num at h1
    linarith

  have h4 : f 1 = (f 1) ^ 3 := by
    specialize h1 1
    norm_num at h1
    linarith

  have h5 : f (-1) = (f (-1)) ^ 3 := by
    specialize h1 (-1)
    norm_num at h1
    linarith

  have h6 : f 0 ≠ f 1 := by
    apply h2
    norm_num

  have h7 : f 0 ≠ f (-1) := by
    apply h2
    norm_num

  have h8 : f 1 ≠ f (-1) := by
    apply h2
    norm_num

  have h9 : f 0 = 0 ∨ f 0 = 1 ∨ f 0 = -1 := by
    have h10 : (f 0) ^ 3 - f 0 = 0 := by
      have h11 : f 0 = (f 0) ^ 3 := h3
      linarith [h11]
    have h11 : f 0 * ((f 0) - 1) * ((f 0) + 1) = 0 := by
      ring_nf at h10 ⊢
      linarith
    cases' (mul_eq_zero.1 h11) with h12 h13
    · cases' (mul_eq_zero.1 h12) with h14 h15
      · left
        linarith
      · right
        left
        linarith
    · right
      right
      linarith

  have h10 : f 1 = 0 ∨ f 1 = 1 ∨ f 1 = -1 := by
    have h11 : (f 1) ^ 3 - f 1 = 0 := by
      have h12 : f 1 = (f 1) ^ 3 := h4
      linarith [h12]
    have h12 : f 1 * ((f 1) - 1) * ((f 1) + 1) = 0 := by
      ring_nf at h11 ⊢
      linarith
    cases' (mul_eq_zero.1 h12) with h13 h14
    · cases' (mul_eq_zero.1 h13) with h15 h16
      · left
        linarith
      · right
        left
        linarith
    · right
      right
      linarith

  have h11 : f (-1) = 0 ∨ f (-1) = 1 ∨ f (-1) = -1 := by
    have h12 : (f (-1)) ^ 3 - f (-1) = 0 := by
      have h13 : f (-1) = (f (-1)) ^ 3 := h5
      linarith [h13]
    have h13 : f (-1) * ((f (-1)) - 1) * ((f (-1)) + 1) = 0 := by
      ring_nf at h12 ⊢
      linarith
    cases' (mul_eq_zero.1 h13) with h14 h15
    · cases' (mul_eq_zero.1 h14) with h16 h17
      · left
        linarith
      · right
        left
        linarith
    · right
      right
      linarith

  rcases h9 with h9 | h9 | h9 <;> rcases h10 with h10 | h10 | h10 <;> rcases h11 with h11 | h11 | h11
    <;> norm_num [h9, h10, h11] at h6 h7 h8 ⊢
    <;> tauto