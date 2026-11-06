import Mathlib

theorem algebra_16358 {p : ℝ} (hp : p > 0) (h : ∀ A B : ℝ × ℝ,
    A ∈ {(x, y) | x ^ 2 / 2 + y ^ 2 = 1} → B ∈ {(x, y) | x ^ 2 / 2 + y ^ 2 = 1} →
    (A.1 - p) * (B.1 - p) = (A.2 - 0) * (B.2 - 0)) :
    p = 2 := by

  have h1 := h (0, 1) (0, 1) (by norm_num) (by norm_num)
  have h2 := h (Real.sqrt 2, 0) (Real.sqrt 2, 0) (by
    have h1 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by linarith)
    have h2 : (Real.sqrt 2) ^ 2 / 2 + (0 : ℝ) ^ 2 = 1 := by
      rw [h1]
      norm_num
    exact h2
  ) (by
    have h1 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by linarith)
    have h2 : (Real.sqrt 2) ^ 2 / 2 + (0 : ℝ) ^ 2 = 1 := by
      rw [h1]
      norm_num
    exact h2
  )

  have h1' : (p) ^ 2 = 1 := by 
    simp at h1 
    nlinarith

  have h2' : (Real.sqrt 2 - p) * (Real.sqrt 2 - p) = 0 := by 
    simp at h2 ⊢ 
    <;> nlinarith

  have h2p : p = Real.sqrt 2 := by 
    have h' : (Real.sqrt 2 - p) ^ 2 = 0 := by
      linarith [h2']
    have h20 : Real.sqrt 2 - p = 0 := by 
      apply pow_eq_zero 
      exact h'
    nlinarith

  have h2p2 : p ^ 2 = 2 := by 
    rw [h2p]
    have h1 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by linarith)
    linarith

  nlinarith