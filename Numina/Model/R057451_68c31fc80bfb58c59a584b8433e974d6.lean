import Mathlib

theorem algebra_219242 {f : ℝ → ℝ} (h : ∀ x, f (Real.sin x - 1) ≥ Real.cos x ^ 2 + 2) :
    ∀ x, -2 ≤ x ∧ x ≤ 0 → f x ≥ -x ^ 2 - 2 * x + 2 := by 
  intro x h_x
  rcases h_x with ⟨hx1, hx2⟩
  have h1 : f x ≥ -x ^ 2 - 2 * x + 2 := by 
    have h2 : Real.sin (Real.arcsin (x + 1)) = x + 1 := by
      apply Real.sin_arcsin
      · nlinarith
      · nlinarith
    have h3 : f (Real.sin (Real.arcsin (x + 1)) - 1) ≥ Real.cos (Real.arcsin (x + 1)) ^ 2 + 2 := h (Real.arcsin (x + 1))
    have h4 : Real.sin (Real.arcsin (x + 1)) - 1 = x := by
      have h5 : Real.sin (Real.arcsin (x + 1)) = x + 1 := h2
      linarith 
    have h6 : Real.cos (Real.arcsin (x + 1)) ^ 2 = 1 - (x + 1) ^ 2 := by 
      have hcos : Real.cos (Real.arcsin (x + 1)) ^ 2 + Real.sin (Real.arcsin (x + 1)) ^ 2 = 1 := by 
        exact Real.cos_sq_add_sin_sq (Real.arcsin (x + 1))
      have hsin : Real.sin (Real.arcsin (x + 1)) = x + 1 := h2
      rw [hsin] at hcos 
      have hcos' : Real.cos (Real.arcsin (x + 1)) ^ 2 = 1 - (x + 1)^2 := by linarith
      linarith 
    have h7 : Real.cos (Real.arcsin (x + 1)) ^ 2 + 2 = -x^2 - 2 * x + 2 := by 
      nlinarith [h6] 
    rw [h4] at h3
    linarith [h3, h7]
  linarith [h1]