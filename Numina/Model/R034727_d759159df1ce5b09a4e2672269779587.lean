import Mathlib

theorem algebra_257089 {f g : ℝ → ℝ} (hfg : ∀ x y, f (x - y) = f x * g y - g x * f y)
    (hf : f (-2) = f 1) (hf' : f 1 ≠ 0) : g 1 + g (-1) = -1 := by
  have h1 : f 0 = 0 := by
    have h00 := hfg 0 0
    norm_num at h00 ⊢
    linarith

  have h2 : g 0 = 1 := by 
    have h3 : f 1 = f 1 * g 0 - g 1 * f 0 := by 
      specialize hfg 1 0 
      norm_num at hfg ⊢ 
      linarith [hfg]
    simp [h1] at h3 
    have h4 : f 1 * (1 - g 0) = 0 := by 
      linarith 
    cases (mul_eq_zero.mp h4) with 
    | inl h => 
      exfalso 
      exact hf' h 
    | inr h => 
      linarith

  have h3 : ∀ a, f (-a) = - f a := by 
    intro a 
    have h4 : f (0 - a) = f 0 * g a - g 0 * f a := hfg 0 a 
    rw [show f (0 - a) = f (-a) by simp, h1, h2] at h4 
    linarith

  have h4 : f (-1) = - f 1 := h3 1 

  have h5 : f (-2) = - f 2 := h3 2 

  have h6 : f 2 = - f 1 := by
    linarith [hf, h5]

  have h7 : f (1 - (-1 : ℝ)) = f 1 * g (-1) - g 1 * f (-1) := by 
    specialize hfg 1 (-1)
    norm_num at hfg ⊢
    linarith [hfg]

  have h8 : f (1 - (-1 : ℝ)) = f 2 := by 
    ring_nf

  rw [h8] at h7
  rw [show f 2 = - f 1 by linarith [h6]] at h7
  rw [show f (-1) = - f 1 by linarith [h4]] at h7

  have h9 : f 1 * (g (-1) + g 1) = - f 1 := by 
    linarith

  have h10 : g (-1) + g 1 = -1 := by 
    apply (mul_left_inj' hf').mp 
    linarith

  linarith [h10]