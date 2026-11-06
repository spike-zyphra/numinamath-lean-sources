import Mathlib

theorem algebra_314688 {f : ℝ → ℝ} (h1 : ∀ x, f (x ^ 3) = f x ^ 3)
    (h2 : ∀ x1 x2, x1 ≠ x2 → f x1 ≠ f x2) :
    f 0 + f 1 + f (-1) = 0 := by

  have h3 : f 0 = f 0 ^ 3 := by
    specialize h1 0
    norm_num at h1
    linarith

  have h4 : f 1 = f 1 ^ 3 := by
    specialize h1 1
    norm_num at h1
    linarith

  have h5 : f (-1) = f (-1) ^ 3 := by
    specialize h1 (-1)
    norm_num at h1
    linarith

  -- Prove the function is injective
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
    have h9 : f 0 ^ 3 - f 0 = 0 := by 
      have h3' : f 0 = f 0 ^ 3 := h3
      linarith
    have h10 : f 0 * (f 0 - 1) * (f 0 + 1) = 0 := by
      nlinarith [h9]
      <;> nlinarith

    cases' (mul_eq_zero.mp h10) with h11 h12
    cases' (mul_eq_zero.mp h11) with h13 h14
    · -- f 0 = 0
      left
      linarith
    · -- f 0 - 1 = 0, so f 0 = 1
      right
      left
      linarith
    · -- f 0 + 1 = 0, so f 0 = -1
      right
      right
      linarith

  have h10 : f 1 = 0 ∨ f 1 = 1 ∨ f 1 = -1 := by
    have h9 : f 1 ^ 3 - f 1 = 0 := by 
      have h4' : f 1 = f 1 ^ 3 := h4
      linarith
    have h10 : f 1 * (f 1 - 1) * (f 1 + 1) = 0 := by
      nlinarith [h9]
    cases' (mul_eq_zero.mp h10) with h11 h12
    cases' (mul_eq_zero.mp h11) with h13 h14
    · -- f 1 = 0
      left
      linarith
    · -- f 1 - 1 = 0, so f 1 = 1
      right
      left
      linarith
    · -- f 1 + 1 = 0, so f 1 = -1
      right
      right
      linarith

  have h11 : f (-1) = 0 ∨ f (-1) = 1 ∨ f (-1) = -1 := by
    have h9 : f (-1) ^ 3 - f (-1) = 0 := by 
      have h5' : f (-1) = f (-1) ^ 3 := h5
      linarith
    have h10 : f (-1) * (f (-1) - 1) * (f (-1) + 1) = 0 := by
      nlinarith [h9]
    cases' (mul_eq_zero.mp h10) with h11 h12
    cases' (mul_eq_zero.mp h11) with h13 h14
    · -- f (-1) = 0
      left
      linarith
    · -- f (-1) - 1 = 0, so f (-1) = 1
      right
      left
      linarith
    · -- f (-1) + 1 = 0, so f (-1) = -1
      right
      right
      linarith

  rcases h9 with h9 | h9 | h9 <;> rcases h10 with h10 | h10 | h10 <;> rcases h11 with h11 | h11 | h11 <;> 
    try { 
      have h0 : f 0 + f 1 + f (-1) = 0 := by
        rw [h9, h10, h11]
        norm_num
      exact h0
    } <;> try { 
      exfalso
      try { 
        tauto
      }
      <;> try { 
        norm_num [h9, h10, h11] at h6 h7 h8
        <;> try { 
          tauto
        }
      }
    }