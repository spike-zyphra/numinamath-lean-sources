import Mathlib

theorem algebra_244526 {G : ℤ → ℤ → ℤ → ℝ}
    (h1 : ∀ a b c n, G (n * a) (n * b) (n * c) = n * G a b c)
    (h2 : ∀ a b c n, G (a + n) (b + n) (c + n) = G a b c + n)
    (h3 : ∀ a b c, G a b c = G c b a) :
    G 89 90 91 = 90 := by
  have eq1 : G 89 90 91 = G (-1) 0 1 + 90 := by
    have h := h2 (-1) 0 1 90
    norm_num at h ⊢
    linarith
  have eq2 : G (-1) 0 1 = G 1 0 (-1) := by
    have h4 := h3 (-1) 0 1
    norm_num at h4 ⊢
    linarith
  have eq3 : G (-1) 0 1 = -1 * G 1 0 (-1) := by
    specialize h1 1 0 (-1) (-1)
    norm_num at h1 ⊢
    linarith
  have eq4 : G 1 0 (-1) = 0 := by
    have eq5 : G (-1) 0 1 = G 1 0 (-1) := by linarith [eq2]
    rw [eq5] at eq3
    linarith
  have eq7 : G (-1) 0 1 = 0 := by
    linarith [eq2, eq4]
  rw [eq7] at eq1
  norm_num at eq1 ⊢
  linarith