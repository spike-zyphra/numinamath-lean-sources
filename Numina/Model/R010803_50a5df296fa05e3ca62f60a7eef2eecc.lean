import Mathlib

theorem algebra_18744 {f : ℝ → ℝ} (h : ∀ x, f x + f (x - 1) = x ^ 2) (h' : f 19 = 94) :
    f 94 = 4561 := by
  have h1 : ∀ (x : ℝ), f (x + 2) = f (x) + 2 * x + 3:= by
    intro x
    have h1 := h (x+1)
    have h2 := h (x+2)
    ring_nf at h1 h2 ⊢
    linarith
  
  have h2 : ∀ n : ℕ, f (19 + 2 * ↑n) = 94 + 39 * n + 2 * n^2 := by
    intro n
    induction n with
    | zero =>
      norm_num
      exact h'
    | succ n ih =>
      have g1 : ((19 + 2 * (n+1 : ℕ)) : ℝ) = (19 + 2 * ↑n) + 2 := by norm_cast
      rw [g1, h1, ih]
      push_cast
      ring
  
  have h3 := h 94
  have h4 := h 93
  norm_num at h3 h4
  
  have h5 : f 93 = 94 + 39 * 37 + 2 * (37^2 : ℕ) := by 
    specialize h2 37
    norm_num at h2 ⊢
    linarith
  
  norm_num at h5
  linarith [h3, h5]