import Mathlib

theorem algebra_205216 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x, f (x + 2) = -f x) :
    f 6 = 0 := by
  have h1 : f 6 = -f 4 := by
    specialize hf 4
    norm_num at hf ⊢
    linarith
  have h2 : f 4 = -f 2 := by
    specialize hf 2
    norm_num at hf ⊢
    linarith
  have h3 : f 2 = -f 0 := by
    specialize hf 0
    norm_num at hf ⊢
    linarith
  have h4 : f 0 = 0 := by
    have hodd_0 : f (- (0 : ℝ)) = -f (0 : ℝ) := by
      apply hodd
    have simp_neg : - (0 : ℝ) = (0 : ℝ) := by
      norm_num
    rw [simp_neg] at hodd_0
    linarith
  rw [h1, h2, h3, h4]
  norm_num