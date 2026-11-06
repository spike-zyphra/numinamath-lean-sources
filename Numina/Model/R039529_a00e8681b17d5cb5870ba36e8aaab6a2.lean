import Mathlib

theorem number_theory_202097 (f : ℚ → ℝ) (h : ∀ a b, 0 < a → 0 < b → f (a * b) = f a + f b)
    (hp : ∀ p, Nat.Prime p → f p = p) :
    f (25 / 11) < 0 := by

  have f1 : f 1 = 0 := by 
    have h1 := h 1 1 (by norm_num) (by norm_num)
    norm_num at h1 ⊢
    linarith

  have f5q : f (5 : ℚ) = 5 := by 
    specialize hp 5 (by norm_num)
    norm_num at hp ⊢
    linarith

  have f25q : f (25 : ℚ) = 10 := by 
    specialize h (5 : ℚ) (5 : ℚ) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith [f5q, h]

  have f11q : f (11 : ℚ) = 11 := by 
    specialize hp 11 (by norm_num)
    norm_num at hp ⊢
    linarith

  have eq2 : f (25 : ℚ) = f (25 / 11) + f (11 : ℚ) := by 
    specialize h (25 / 11 : ℚ) (11 : ℚ) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith

  linarith [eq2, f25q, f11q]