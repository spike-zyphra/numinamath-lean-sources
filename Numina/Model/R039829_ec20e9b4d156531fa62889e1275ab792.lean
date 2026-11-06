import Mathlib

theorem algebra_10200 (f : ℝ → ℝ → ℝ) (hf1 : ∀ r, f r 0 = r) (hf2 : ∀ r s, f r s = f s r) (hf3 : ∀ r s, f (r + 1) s = f r s + s + 1) : f 11 5 = 71 := by
  have eq1 : f 11 5 = f 10 5 + 5 + 1 := by
    specialize hf3 10 5
    norm_num at hf3 ⊢
    linarith
  have eq2 : f 10 5 = f 9 5 + 5 + 1 := by
    specialize hf3 9 5
    norm_num at hf3 ⊢
    linarith
  have eq3 : f 9 5 = f 8 5 + 5 + 1 := by
    specialize hf3 8 5
    norm_num at hf3 ⊢
    linarith
  have eq4 : f 8 5 = f 7 5 + 5 + 1 := by
    specialize hf3 7 5
    norm_num at hf3 ⊢
    linarith
  have eq5 : f 7 5 = f 6 5 + 5 + 1 := by
    specialize hf3 6 5
    norm_num at hf3 ⊢
    linarith
  have eq6 : f 6 5 = f 5 5 + 5 + 1 := by
    specialize hf3 5 5
    norm_num at hf3 ⊢
    linarith
  have eq7 : f 5 5 = f 4 5 + 5 + 1 := by
    specialize hf3 4 5
    norm_num at hf3 ⊢
    linarith
  have eq8 : f 4 5 = f 3 5 + 5 + 1 := by
    specialize hf3 3 5
    norm_num at hf3 ⊢
    linarith
  have eq9 : f 3 5 = f 2 5 + 5 + 1 := by
    specialize hf3 2 5
    norm_num at hf3 ⊢
    linarith
  have eq10 : f 2 5 = f 1 5 + 5 + 1 := by
    specialize hf3 1 5
    norm_num at hf3 ⊢
    linarith
  have eq11 : f 1 5 = f 0 5 + 5 + 1 := by
    specialize hf3 0 5
    norm_num at hf3 ⊢
    linarith
  have eq12 : f 0 5 = f 5 0 := by 
    specialize hf2 0 5
    norm_num at hf2 ⊢
    linarith
  have eq13 : f 5 0 = (5 : ℝ) := by 
    specialize hf1 5
    norm_num at hf1 ⊢
    linarith
  norm_num [eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12, eq13]