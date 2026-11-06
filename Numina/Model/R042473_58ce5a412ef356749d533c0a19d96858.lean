import Mathlib

theorem algebra_244627 {g : ℤ → ℤ → ℤ → ℝ}
    (h1 : ∀ a b c n, g (n * a) (n * b) (n * c) = n * g a b c)
    (h2 : ∀ a b c n, g (a + n) (b + n) (c + n) = g a b c + n)
    (h3 : ∀ a b c, g a b c = g c b a) :
    g 14 15 16 = 15 := by

  have eq1 : g 14 15 16 = g (-1) 0 1 + 15 := by
    specialize h2 (-1) 0 1 15 
    norm_num at h2 ⊢ 
    linarith

  have eq2 : g (-1) 0 1 = g 1 0 (-1) := by
    specialize h3 (-1) 0 1 
    norm_num at h3 ⊢ 
    linarith

  have eq3 : g (-1) 0 1 = - g 1 0 (-1) := by 
    specialize h1 1 0 (-1) (-1)
    norm_num at h1 ⊢
    linarith

  have eq4 : g 1 0 (-1) = 0 := by
    linarith [eq2, eq3]

  linarith [eq1, eq2, eq4]