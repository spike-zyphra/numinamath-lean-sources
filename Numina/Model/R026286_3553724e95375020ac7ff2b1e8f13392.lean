import Mathlib

theorem algebra_292439 {f : ℝ → ℝ} (h : ∀ x, f (x ^ 3) = f x ^ 3) (h' : ∀ x y, x ≠ y → f x ≠ f y) :
    f 0 + f 1 + f (-1) = 0 := by
  have h1 : f 0 = f 0 ^ 3 := by 
    specialize h 0 
    norm_num at h 
    all_goals linarith 
  have h2 : f 1 = f 1 ^ 3 := by 
    specialize h 1 
    norm_num at h 
    all_goals linarith 
  have h3 : f (-1) = f (-1) ^ 3 := by 
    specialize h (-1) 
    norm_num at h 
    all_goals linarith 
  have h4 : f 0 ≠ f 1 := by 
    apply h' 
    norm_num 
  have h5 : f 0 ≠ f (-1) := by 
    apply h' 
    norm_num 
  have h6 : f 1 ≠ f (-1) := by 
    apply h' 
    norm_num 
  have h7 : f 0 * (f 0 - 1) * (f 0 + 1) = 0 := by
    have h8 : f 0 ^ 3 - f 0 = 0 := by 
      linarith [h1]
    have : f 0 * (f 0 - 1) * (f 0 + 1) = 0 := by
      ring_nf at h8 ⊢ 
      linarith 
    assumption 
  have h8 : f 1 * (f 1 - 1) * (f 1 + 1) = 0 := by
    have h9 : f 1 ^ 3 - f 1 = 0 := by 
      linarith [h2]
    have : f 1 * (f 1 - 1) * (f 1 + 1) = 0 := by
      ring_nf at h9 ⊢ 
      linarith 
    assumption 
  have h9 : f (-1) * (f (-1) - 1) * (f (-1) + 1) = 0 := by
    have h10 : f (-1) ^ 3 - f (-1) = 0 := by 
      linarith [h3]
    have : f (-1) * (f (-1) - 1) * (f (-1) + 1) = 0 := by
      ring_nf at h10 ⊢ 
      linarith 
    assumption 
  have h10 : f 0 = 0 ∨ f 0 = 1 ∨ f 0 = -1 := by 
    cases (mul_eq_zero.mp h7) with
    | inl h11 =>
      cases (mul_eq_zero.mp h11) with
      | inl h12 =>
        left 
        linarith 
      | inr h13 =>
        right 
        left 
        linarith 
    | inr h11 =>
      right 
      right 
      linarith 
  have h11 : f 1 = 0 ∨ f 1 = 1 ∨ f 1 = -1 := by 
    cases (mul_eq_zero.mp h8) with
    | inl h12 =>
      cases (mul_eq_zero.mp h12) with
      | inl h13 =>
        left 
        linarith 
      | inr h14 =>
        right 
        left 
        linarith 
    | inr h12 =>
      right 
      right 
      linarith 
  have h12 : f (-1) = 0 ∨ f (-1) = 1 ∨ f (-1) = -1 := by 
    cases (mul_eq_zero.mp h9) with
    | inl h13 =>
      cases (mul_eq_zero.mp h13) with
      | inl h14 =>
        left 
        linarith 
      | inr h15 =>
        right 
        left 
        linarith 
    | inr h13 =>
      right 
      right 
      linarith 
  rcases h10 with (h10 | h10 | h10) <;> rcases h11 with (h11 | h11 | h11) <;> rcases h12 with (h12 | h12 | h12) <;> 
    ( 
      norm_num [h10, h11, h12] at *
      <;> tauto 
    )