import Mathlib

theorem algebra_190349 (f : ℝ → ℝ) (h1 : ∀ x, f (x ^ 3) = f x ^ 3)
    (h2 : ∀ x1 x2, x1 ≠ x2 → f x1 ≠ f x2) :
    f 0 + f 1 + f (-1) = 0 := by

  have h0 : f 0 = f 0 ^ 3 := by
    specialize h1 0
    norm_num at h1
    linarith

  have h1_eq : f 1 = f 1 ^ 3 := by
    specialize h1 1
    norm_num at h1
    linarith

  have h_1_eq : f (-1) = f (-1) ^ 3 := by
    specialize h1 (-1)
    norm_num at h1
    linarith

  have h0_eq : f 0 = 0 ∨ f 0 = 1 ∨ f 0 = -1 := by
    have h0_CUBE : f 0 ^ 3 - f 0 = 0 := by linarith [h0]
    have : f 0 * (f 0 ^ 2 - 1) = 0 := by
      ring_nf at h0_CUBE ⊢
      linarith
    cases (mul_eq_zero.mp this) with
    | inl h0_0 => 
      left
      exact h0_0
    | inr h0_sq_minus_1 => 
      have h0_sq : f 0 ^ 2 = 1 := by linarith
      have h0_1_or_neg1 : f 0 = 1 ∨ f 0 = -1 := by
        have h : f 0 ^ 2 - 1 = 0 := by linarith
        have : (f 0 - 1) * (f 0 + 1) = 0 := by 
          ring_nf at h ⊢
          linarith
        cases (mul_eq_zero.mp this) with
        | inl h1 => 
          left
          linarith
        | inr h2 => 
          right
          linarith
      cases h0_1_or_neg1 with
      | inl h1 => 
        right
        left
        exact h1
      | inr h2 => 
        right
        right
        linarith

  have h1_eq_0_or_1_or_neg1 : f 1 = 0 ∨ f 1 = 1 ∨ f 1 = -1 := by
    have h1_CUBE : f 1 ^ 3 - f 1 = 0 := by linarith [h1_eq]
    have : f 1 * (f 1 ^ 2 - 1) = 0 := by 
      ring_nf at h1_CUBE ⊢
      linarith
    cases (mul_eq_zero.mp this) with
    | inl h1_0 => 
      left
      exact h1_0
    | inr h1_sq_minus_1 => 
      have h1_sq : f 1 ^ 2 = 1 := by linarith
      have h1_1_or_neg1 : f 1 = 1 ∨ f 1 = -1 := by
        have h : f 1 ^ 2 - 1 = 0 := by linarith
        have : (f 1 - 1) * (f 1 + 1) = 0 := by 
          ring_nf at h ⊢
          linarith
        cases (mul_eq_zero.mp this) with
        | inl h1 => 
          left
          linarith
        | inr h2 => 
          right
          linarith
      cases h1_1_or_neg1 with
      | inl h1 => 
        right
        left
        exact h1
      | inr h2 => 
        right
        right
        linarith

  have h_1_eq_0_or_1_or_neg1 : f (-1) = 0 ∨ f (-1) = 1 ∨ f (-1) = -1 := by
    have h_1_CUBE : f (-1) ^ 3 - f (-1) = 0 := by linarith [h_1_eq]
    have : f (-1) * (f (-1) ^ 2 - 1) = 0 := by 
      ring_nf at h_1_CUBE ⊢
      linarith
    cases (mul_eq_zero.mp this) with
    | inl h_1_0 => 
      left
      exact h_1_0
    | inr h_1_sq_minus_1 => 
      have h_1_sq : f (-1) ^ 2 = 1 := by linarith
      have h_1_1_or_neg1 : f (-1) = 1 ∨ f (-1) = -1 := by
        have h : f (-1) ^ 2 - 1 = 0 := by linarith
        have : (f (-1) - 1) * (f (-1) + 1) = 0 := by 
          ring_nf at h ⊢
          linarith
        cases (mul_eq_zero.mp this) with
        | inl h1 => 
          left
          linarith
        | inr h2 => 
          right
          linarith
      cases h_1_1_or_neg1 with
      | inl h1 => 
        right
        left
        exact h1
      | inr h2 => 
        right
        right
        linarith

  rcases h0_eq with h0_0 | h0_1 | h0_neg1
  · -- Case f(0) = 0
    rcases h1_eq_0_or_1_or_neg1 with h1_0 | h1_1 | h1_neg1
    · -- This case is impossible because f(0) ≠ f(1) as 0 ≠ 1
      exfalso
      have h_inj_0_1 : f 1 ≠ f 0 := by
        apply h2
        norm_num
      rw [h0_0, h1_0] at h_inj_0_1
      norm_num at h_inj_0_1
    · -- Case f(1) = 1
      rcases h_1_eq_0_or_1_or_neg1 with h_1_0 | h_1_1 | h_1_neg1
      · -- This case is impossible because f(-1) ≠ f(0) as -1 ≠ 0
        exfalso
        have h_inj_0_neg1 : f (-1) ≠ f 0 := by
          apply h2
          norm_num
        rw [h0_0, h_1_0] at h_inj_0_neg1
        norm_num at h_inj_0_neg1
      · -- This case is impossible because f(-1) ≠ f(1) as -1 ≠ 1
        exfalso
        have h_inj_1_neg1 : f (-1) ≠ f 1 := by
          apply h2
          norm_num
        rw [h1_1, h_1_1] at h_inj_1_neg1
        norm_num at h_inj_1_neg1
      · -- Case f(-1) = -1
        have h_sum : f 0 + f 1 + f (-1) = 0 + 1 + (-1) := by
          rw [h0_0, h1_1, h_1_neg1]
        linarith
    · -- Case f(1) = -1
      rcases h_1_eq_0_or_1_or_neg1 with h_1_0 | h_1_1 | h_1_neg1
      · -- This case is impossible because f(-1) ≠ f(0) as -1 ≠ 0
        exfalso
        have h_inj_0_neg1 : f (-1) ≠ f 0 := by
          apply h2
          norm_num
        rw [h0_0, h_1_0] at h_inj_0_neg1
        norm_num at h_inj_0_neg1
      · -- Case f(-1) = 1
        have h_sum : f 0 + f 1 + f (-1) = 0 + (-1) + 1 := by
          rw [h0_0, h1_neg1, h_1_1]
        linarith
      · -- This case is impossible because f(-1) ≠ f(1) as -1 ≠ 1
        exfalso
        have h_inj_1_neg1 : f (-1) ≠ f 1 := by
          apply h2
          norm_num
        rw [h1_neg1, h_1_neg1] at h_inj_1_neg1
        norm_num at h_inj_1_neg1
  · -- Case f(0) = 1
    rcases h1_eq_0_or_1_or_neg1 with h1_0 | h1_1 | h1_neg1
    · -- Case f(1) = 0
      rcases h_1_eq_0_or_1_or_neg1 with h_1_0 | h_1_1 | h_1_neg1
      · -- This case is impossible because f(-1) ≠ f(1) as -1 ≠ 1
        exfalso
        have h_inj_1_neg1 : f (-1) ≠ f 1 := by
          apply h2
          norm_num
        rw [h1_0, h_1_0] at h_inj_1_neg1
        norm_num at h_inj_1_neg1
      · -- This case is impossible because f(-1) ≠ f(0) as -1 ≠ 0
        exfalso
        have h_inj_0_neg1 : f (-1) ≠ f 0 := by
          apply h2
          norm_num
        rw [h0_1, h_1_1] at h_inj_0_neg1
        norm_num at h_inj_0_neg1
      · -- Case f(-1) = -1
        have h_sum : f 0 + f 1 + f (-1) = 1 + 0 + (-1) := by
          rw [h0_1, h1_0, h_1_neg1]
        linarith
    · -- This case is impossible because f(1) ≠ f(0) as 1 ≠ 0
      exfalso
      have h_inj_0_1 : f 1 ≠ f 0 := by
        apply h2
        norm_num
      rw [h0_1, h1_1] at h_inj_0_1
      norm_num at h_inj_0_1
    · -- Case f(1) = -1
      rcases h_1_eq_0_or_1_or_neg1 with h_1_0 | h_1_1 | h_1_neg1
      · -- Case f(-1) = 0
        have h_sum : f 0 + f 1 + f (-1) = 1 + (-1) + 0 := by
          rw [h0_1, h1_neg1, h_1_0]
        linarith
      · -- This case is impossible because f(-1) ≠ f(0) as -1 ≠ 0
        exfalso
        have h_inj_0_neg1 : f (-1) ≠ f 0 := by
          apply h2
          norm_num
        rw [h0_1, h_1_1] at h_inj_0_neg1
        norm_num at h_inj_0_neg1
      · -- This case is impossible because f(-1) ≠ f(1) as -1 ≠ 1
        exfalso
        have h_inj_1_neg1 : f (-1) ≠ f 1 := by
          apply h2
          norm_num
        rw [h1_neg1, h_1_neg1] at h_inj_1_neg1
        norm_num at h_inj_1_neg1
  · -- Case f(0) = -1
    rcases h1_eq_0_or_1_or_neg1 with h1_0 | h1_1 | h1_neg1
    · -- Case f(1) = 0
      rcases h_1_eq_0_or_1_or_neg1 with h_1_0 | h_1_1 | h_1_neg1
      · -- This case is impossible because f(-1) ≠ f(1) as -1 ≠ 1
        exfalso
        have h_inj_1_neg1 : f (-1) ≠ f 1 := by
          apply h2
          norm_num
        rw [h1_0, h_1_0] at h_inj_1_neg1
        norm_num at h_inj_1_neg1
      · -- Case f(-1) = 1
        have h_sum : f 0 + f 1 + f (-1) = -1 + 0 + 1 := by
          rw [h0_neg1, h1_0, h_1_1]
        linarith
      · -- This case is impossible because f(-1) ≠ f(0) as -1 ≠ 0
        exfalso
        have h_inj_0_neg1 : f (-1) ≠ f 0 := by
          apply h2
          norm_num
        rw [h0_neg1, h_1_neg1] at h_inj_0_neg1
        norm_num at h_inj_0_neg1
    · -- Case f(1) = 1
      rcases h_1_eq_0_or_1_or_neg1 with h_1_0 | h_1_1 | h_1_neg1
      · -- Case f(-1) = 0
        have h_sum : f 0 + f 1 + f (-1) = -1 + 1 + 0 := by
          rw [h0_neg1, h1_1, h_1_0]
        linarith
      · -- This case is impossible because f(-1) ≠ f(1) as -1 ≠ 1
        exfalso
        have h_inj_1_neg1 : f (-1) ≠ f 1 := by
          apply h2
          norm_num
        rw [h1_1, h_1_1] at h_inj_1_neg1
        norm_num at h_inj_1_neg1
      · -- This case is impossible because f(-1) ≠ f(0) as -1 ≠ 0
        exfalso
        have h_inj_0_neg1 : f (-1) ≠ f 0 := by
          apply h2
          norm_num
        rw [h0_neg1, h_1_neg1] at h_inj_0_neg1
        norm_num at h_inj_0_neg1
    · -- This case is impossible because f(1) ≠ f(0) as 1 ≠ 0
      exfalso
      have h_inj_0_1 : f 1 ≠ f 0 := by
        apply h2
        norm_num
      rw [h0_neg1, h1_neg1] at h_inj_0_1
      norm_num at h_inj_0_1