import Mathlib

/-
Problem:

Given that \(f(x)= \begin{cases} 2^{x}-3 & ,x > 0\\ g(x) & ,x < 0 \end{cases}\) is an odd function, find the value of \(f(g(-2))\).
-/

theorem algebra_9269 {f g : ℝ → ℝ} (hf : ∀ x, x > 0 → f x = 2 ^ x - 3)
    (hg : ∀ x, x < 0 → f x = g x) (hodd : ∀ x, - f (-x) = (f x)) :
    f (g (-2)) = 1 := by
  -- From the definition of f and hodd, we can deduce the value of f at some points
  have h1 : f (-2) = g (-2) := by
    apply hg
    norm_num
  -- Compute f(2)
  have h2 : f (2 : ℝ) = 1 := by
    specialize hf 2 (by norm_num)
    rw [hf]
    norm_num
  -- Use the odd function property for x = 2: -f(-2) = f(2)
  have h3 : - f (-2) = f (2 : ℝ) := by
    specialize hodd 2
    simpa using hodd
  -- From h2 and h3, we can find f(-2)
  have h4 : f (-2) = -1 := by
    linarith [h2, h3]
  -- Since f(-2) = g(-2), we have g(-2) = -1
  have h5 : g (-2) = -1 := by
    linarith [h1, h4]
  -- Therefore, we need to compute f(-1) where -1 < 0.
  have h7 : f (g (-2)) = f (-1) := by
    rw [h5]
  -- Compute f(-1) using the odd function property for x = 1
  have h8 : f (-1) = 1 := by
    have h9 : - f (-(-1 : ℝ)) = f (-1 : ℝ) := by
      specialize hodd (-1)
      simpa using hodd
    have h10 : f (1 : ℝ) = -1 := by
      specialize hf 1 (by norm_num)
      rw [hf]
      norm_num
    have h11 : -f (1 : ℝ) = f (-1 : ℝ) := by
      have h12 : -f (-(-1 : ℝ)) = f (-1 : ℝ) := h9
      have h13 : -(-1 : ℝ) = (1 : ℝ) := by norm_num
      rw [h13] at h12
      linarith
    linarith [h10, h11]
  -- The final result
  rw [h7, h8]