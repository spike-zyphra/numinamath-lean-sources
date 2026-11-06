import Mathlib

theorem algebra_244429 {f : ℤ → ℤ → ℤ → ℝ}
    (h1 : ∀ a b c n, f (n * a) (n * b) (n * c) = n * f a b c)
    (h2 : ∀ a b c n, f (a + n) (b + n) (c + n) = f a b c + n)
    (h3 : ∀ a b c, f a b c = f c b a) :
    f 24 25 26 = 25 := by
  have eq1 : f (-1 : ℤ) (0 : ℤ) (1 : ℤ) = f 24 25 26 - 25 := by
    specialize h2 24 25 26 (-25 : ℤ)
    norm_num at h2 ⊢
    linarith
  have eq2 : f 1 (0 : ℤ) (-1 : ℤ) = 0 := by
    have eq3 : f (-1 : ℤ) (0 : ℤ) (1 : ℤ) = - f 1 0 (-1 : ℤ) := by
      specialize h1 1 0 (-1 : ℤ) (-1 : ℤ)
      norm_num at h1 ⊢
      linarith
    have eq4 : f (-1 : ℤ) (0 : ℤ) (1 : ℤ) = f 1 0 (-1 : ℤ) := by
      specialize h3 (-1 : ℤ) (0 : ℤ) (1 : ℤ)
      norm_num at h3 ⊢
      linarith
    linarith [eq3, eq4]
  have eq3 : f (-1 : ℤ) (0 : ℤ) (1 : ℤ) = 0 := by
    have h4 : f (-1 : ℤ) (0 : ℤ) (1 : ℤ) = f 1 (0 : ℤ) (-1 : ℤ) := by
      specialize h3 (-1 : ℤ) (0 : ℤ) (1 : ℤ)
      norm_num at h3 ⊢
      linarith
    linarith [h4, eq2]
  linarith [eq1, eq3]