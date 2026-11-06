import Mathlib

theorem algebra_282837 {f : ℝ → ℝ} (h : ∀ a b, f (a * f b) = a * b) :
    Real.sqrt ((f 2009)^2) = 2009 := by
  have h0 : f 0 = 0 := by
    have h1 := h 0 0
    norm_num at h1
    linarith
  have h2 : ∀ x, f (f x) = x := by
    intro x
    specialize h 1 x
    norm_num at h
    linarith
  have h3 : ∀ x, f x = (f 1) * x := by
    intro x
    have h4 := h x (f 1)
    have h5 : f (x * f (f 1)) = x * (f 1) := by
      simpa using h4
    have h6 : f (f 1) = 1 := by
      apply h2 1
    rw [h6] at h5
    have h8 : f x = (f 1) * x := by
      simp at h5 ⊢
      linarith
    linarith
  have h7 : (f 1 : ℝ) ^ 2 = 1 := by
    specialize h2 1
    have h8 : f (f 1) = 1 := by
      simpa using h2
    have h9 : f (f 1) = (f 1) * (f 1) := by
      specialize h3 (f 1)
      linarith
    rw [h9] at h8
    nlinarith
  have h15 : (f 2009 : ℝ) ^ 2 = (2009 : ℝ) ^ 2 := by
    have h16 : f 2009 = (f 1) * (2009 : ℝ) := by
      specialize h3 2009
      linarith
    rw [h16]
    have h17 : (f 1 : ℝ) ^ 2 = 1 := h7
    calc
      ((f 1 : ℝ) * (2009 : ℝ)) ^ 2 = (f 1 : ℝ) ^ 2 * (2009 : ℝ) ^ 2 := by ring
      _ = 1 * (2009 : ℝ) ^ 2 := by rw [h17]
      _ = (2009 : ℝ) ^ 2 := by ring
  have h10 : Real.sqrt ((f 2009 : ℝ) ^ 2) = (2009 : ℝ) := by
    have h15' : (f 2009 : ℝ) ^ 2 = (2009 : ℝ) ^ 2 := h15
    have h26 : Real.sqrt ((f 2009 : ℝ) ^ 2) = Real.sqrt ((2009 : ℝ) ^ 2) := by
      rw [h15']
    have h27 : Real.sqrt ((2009 : ℝ) ^ 2) = (2009 : ℝ) := by
      rw [Real.sqrt_sq (show (0 : ℝ) ≤ (2009 : ℝ) by norm_num)]
    rw [h27] at h26
    linarith
  exact h10