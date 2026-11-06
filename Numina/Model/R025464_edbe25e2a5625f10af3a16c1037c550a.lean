import Mathlib

theorem algebra_234616 {a : ℕ → ℤ} (h : a 0 = 3) (h' : a 1 = 7)
    (h'' : ∀ n, a (n + 1) = a n - a (n - 1)) :
    a 99 = -3 := by 
  have h1 := h'' 0
  simp at h1
  omega