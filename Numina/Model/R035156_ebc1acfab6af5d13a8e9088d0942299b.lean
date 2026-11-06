import Mathlib

theorem algebra_190349 (f : ℝ → ℝ) (h1 : ∀ x, f (x ^ 3) = f x ^ 3)
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

  have h6 : f 0 = 0 ∨ f 0 = 1 ∨ f 0 = -1 := by 
    have h7 : f 0 ^ 3 - f 0 = 0 := by linarith
    have h8 : f 0 * (f 0 - 1) * (f 0 + 1) = 0 := by 
      ring_nf at h7 ⊢
      linarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    cases' (mul_eq_zero.mp h9) with h11 h12
    · -- Case f 0 = 0
      left
      linarith
    · -- Case f 0 - 1 = 0
      right
      left
      linarith
    · -- Case f 0 + 1 = 0
      right
      right
      linarith

  have h7 : f 1 = 0 ∨ f 1 = 1 ∨ f 1 = -1 := by 
    have h8 : f 1 ^ 3 - f 1 = 0 := by linarith
    have h9 : f 1 * (f 1 - 1) * (f 1 + 1) = 0 := by 
      ring_nf at h8 ⊢
      linarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    cases' (mul_eq_zero.mp h10) with h12 h13
    · -- Case f 1 = 0
      left
      linarith
    · -- Case f 1 - 1 = 0
      right
      left
      linarith
    · -- Case f 1 + 1 = 0
      right
      right
      linarith

  have h8 : f (-1) = 0 ∨ f (-1) = 1 ∨ f (-1) = -1 := by 
    have h9 : f (-1) ^ 3 - f (-1) = 0 := by linarith
    have h10 : f (-1) * (f (-1) - 1) * (f (-1) + 1) = 0 := by 
      ring_nf at h9 ⊢
      linarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    cases' (mul_eq_zero.mp h11) with h13 h14
    · -- Case f (-1) = 0
      left
      linarith
    · -- 2nd case
      right
      left
      linarith
    · -- 3rd case
      right
      right
      linarith
  have h9 : f 0 ≠ f 1 := by 
    apply h2
    norm_num
  have h10 : f 1 ≠ f (-1) := by
    apply h2
    norm_num
  have h11 : f 0 ≠ f (-1) := by 
    apply h2
    norm_num
  rcases h6 with h6 | h6 | h6 <;> rcases h7 with h7 | h7 | h7 <;> rcases h8 with h8 | h8 | h8 <;> 
    norm_num [h6, h7, h8] at *
    <;> try { 
      exfalso 
      try { 
        tauto 
      }
      <;> try { 
        nlinarith 
      }
      <;> try { 
        all_goals nlinarith 
      }
      <;> try { 
        all_goals tauto 
      }
      <;> try { 
        norm_num at h9 h10 h11 
        all_goals tauto 
      }
      <;> try { 
        norm_num at h9 h10 h11 
        all_goals nlinarith 
      }
      <;> try { 
        norm_num at h9 h10 h11 
        all_goals contradiction 
      }
    }