import Mathlib


theorem number_theory_608006 (f : ℤ → ℤ) (hf : ∀ x, 0 < f x)
(h : ∀ x y, x ≤ y → f x ≤ f y) (h1 : ∀ m n, IsCoprime m n → f (m * n) = f m * f n) : f 8 * f 13 ≥ (f 10) ^ 2:= by

  have h2 : (70 : ℤ) ≤ (72 : ℤ) := by norm_num
  have h3 : f 70 ≤ f 72 := h 70 72 h2
  have h4 : f 70 = f 7 * f 10 := by
    specialize h1 7 10 (by norm_num [IsCoprime])
    norm_num at h1 ⊢
    all_goals nlinarith
  have h5 : f 72 = f 8 * f 9 := by
    specialize h1 8 9 (by norm_num [IsCoprime])
    norm_num at h1 ⊢
    all_goals nlinarith

  have h6 : (90 : ℤ) ≤ (91 : ℤ) := by norm_num
  have h7 : f 90 ≤ f 91 := h 90 91 h6
  have h8 : f 90 = f 9 * f 10 := by
    specialize h1 9 10 (by norm_num [IsCoprime])
    norm_num at h1 ⊢
    all_goals nlinarith
  have h9 : f 91 = f 13 * f 7 := by
    specialize h1 13 7 (by norm_num [IsCoprime])
    norm_num at h1 ⊢
    all_goals nlinarith

  have h10 : 0 < f 7 := hf 7
  have h11 : 0 < f 10 := hf 10
  have h12 : 0 < f 8 := hf 8
  have h13 : 0 < f 9 := hf 9
  have h14 : 0 < f 13 := hf 13

  rw [h4, h5] at h3
  rw [h8, h9] at h7

  nlinarith [mul_pos (hf 7) (hf 10), mul_pos (hf 8) (hf 9), mul_pos (hf 9) (hf 10), mul_pos (hf 13) (hf 7)]