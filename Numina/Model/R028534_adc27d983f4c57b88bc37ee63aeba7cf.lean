import Mathlib

theorem algebra_152457 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (hsymm : ∀ x, f (2 - x) = f (2 + x)) (hf : ∀ x ∈ Set.Icc 0 2, f x = x + 1) :
    f (-100) + f (-101) = 2 := by
  have h1 : f 0 = 1 := by
    specialize hf 0 (by norm_num)
    norm_num at hf ⊢
    linarith
  have h2 : f 0 = 0 := by 
    specialize hodd 0 
    norm_num at hodd ⊢ 
    linarith
  linarith