import Mathlib

theorem algebra_171976 (f : ℝ → ℝ) (h : ∀ x y, f (x + y) = f x + f y + x * y) (h' : f 4 = 10) :
    f 2001 = 2003001 := by
  have f0 : f 0 = 0 := by
    have eq := h 0 0
    norm_num at eq
    linarith

  have eq1 := h 2 2
  have h1 : f 4 = 2 * f 2 + 4 := by
    rw [show (4 : ℝ) = (2 : ℝ) + (2 : ℝ) by norm_num] at h'
    norm_num at h' eq1
    linarith

  have h2 : f 2 = 3 := by
    linarith [h1, h']

  have eq2 := h 1 1
  have h3 : f 1 = 1 := by
    rw [show (2 : ℝ) = (1 : ℝ) + (1 : ℝ) by norm_num] at h2
    norm_num at eq2 h2
    linarith

  have h3x : ∀ (n : ℕ), f ((↑n : ℝ) ) = (↑n ^ 2 + ↑n) / 2 := by 
    intro n 
    induction n with 
    | zero =>
      simp [f0]
    | succ n ih =>
      have eq11 : (↑(n + 1 : ℕ) : ℝ) = (↑n : ℝ) + 1 := by 
        simp 
        <;> ring 
      rw [eq11]
      rw [h ((↑n : ℝ)) 1]
      rw [ih]
      simp [h3]
      <;> ring

  have eq12 := h3x 2001
  norm_num at eq12 ⊢
  linarith