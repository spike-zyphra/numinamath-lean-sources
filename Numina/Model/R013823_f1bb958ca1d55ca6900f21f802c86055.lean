import Mathlib

theorem algebra_317807 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (heven : ∀ x, f (x + 1) = f (-x + 1)) (hf : ∀ x ∈ Set.Icc (-1) 0, f x = x ^ 3) :
    f (9 / 2) = 1 / 8 := by
  have h1 : f (9 / 2) = f (-5 / 2) := by
    have h2 : f (7 / 2 + 1) = f (- (7 / 2) + 1) := by
      apply heven
    norm_num at h2 ⊢
    linarith
  have h2 : f (-5 / 2) = - f (5 / 2) := by
    specialize hodd (5 / 2)
    norm_num at hodd ⊢
    linarith
  have h3 : f (5 / 2) = f (-1 / 2) := by
    have h4 : f (3 / 2 + 1) = f (- (3 / 2) + 1) := by
      apply heven
    norm_num at h4 ⊢
    linarith
  -- f(-1/2 ) using f is odd
  have h4 : f (-1 / 2) = - f (1 / 2) := by
    specialize hodd (1 / 2)
    norm_num at hodd ⊢
    linarith
  -- f(-1/2) = (-1/2)^3
  have h5 : f (-1 / 2) = (-1 / 2) ^ 3 := by
    apply hf
    norm_num
  -- Therefore f(1/2 ) = 1/8
  have h5' : f (1 / 2) = 1 / 8 := by
    linarith [h4, h5]
  -- Therefore f(9/2 ) = 1/8
  linarith [h1, h2, h3, h5', h4]