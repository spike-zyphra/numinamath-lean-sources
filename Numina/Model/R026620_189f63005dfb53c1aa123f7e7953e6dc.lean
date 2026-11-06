import Mathlib

theorem algebra_237019 (a : ℕ → ℤ) (ha : ∀ n, a (n + 2) = a n + a (n + 1))
    (ha1 : ∀ n, 0 < a n) (ha2 : a 7 = 400) :
    a 2 ≥ 35 := by
  have h1 : a 2 = a 0 + a 1 := by 
    specialize ha 0
    norm_num at ha ⊢
    linarith
  have h2 : a 3 = a 1 + a 2 := by 
    specialize ha 1
    norm_num at ha ⊢
    linarith
  have h3 : a 3 = a 0 + 2 * a 1 := by
    rw [h2, h1]
    ring
  have h4 : a 4 = a 2 + a 3 := by
    specialize ha 2
    norm_num at ha ⊢
    linarith
  have h5 : a 4 = 2 * a 0 + 3 * a 1 := by 
    rw [h4, h3, h1]
    ring
  have h6 : a 5 = a 3 + a 4 := by
    specialize ha 3
    norm_num at ha ⊢
    linarith
  have h7 : a 5 = 3 * a 0 + 5 * a 1 := by 
    rw [h6, h5, h3]
    ring
  have h8 : a 6 = a 4 + a 5 := by
    specialize ha 4
    norm_num at ha ⊢
    linarith
  have h9 : a 6 = 5 * a 0 + 8 * a 1 := by 
    rw [h8,  h7,  h5]
    ring
  have h10 : a 7 = a 5 + a 6 := by
    specialize ha 5
    norm_num at ha ⊢
    linarith
  have h11 : a 7 = 8 * a 0 + 13 * a 1 := by 
    rw [h10,  h9,  h7]
    ring
  rw [h11] at ha2
  have ha0 : 0 < a 0 := by apply ha1 0
  have ha1' : 0 < a 1 := by apply ha1 1
  omega