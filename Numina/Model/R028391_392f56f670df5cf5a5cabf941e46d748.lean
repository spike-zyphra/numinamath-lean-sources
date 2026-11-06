import Mathlib
theorem algebra_607621 {f : ℝ → ℝ} : (∀ x y, f x * f y - f (x * y) = x + y) ↔
∀ x, f x = x + 1:= by
  constructor
  · -- Assume functional equation, prove f(x) = x + 1
    intro h
    have h1 : f 0 = 1 := by
      have h1 := h 0 0 
      simp at h1 
      have h2 : f 0 * (f 0 - 1) = 0 := by
        linarith 
      cases' (mul_eq_zero.mp h2) with h3 h4
      · -- If f(0) = 0, contradiction 
        have h4 := h 1 0 
        simp [h3] at h4 
        all_goals linarith 
      · -- If f(0) - 1 = 0 
        linarith 
    have h2 : f 1 = 2 := by 
      have h4 := h 1 1 
      have h5 : f 1 * f 1 - f (1 * 1) = 1 + 1 := by 
        simpa using h4 
      have h6 : f (1 * 1) = f 1 := by 
          simp 
      rw [h6] at h5 
      have h7 : (f 1 - 2) * (f 1 + 1) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h7) with h8 h9 
      · -- If f 1 - 2 = 0 
        linarith 
      · -- If f 1 + 1 = 0 
        have h10 : f 1 = -1 := by linarith 
        have h11 := h 0 1 
        simp [h1, h10] at h11 
        all_goals linarith 
    intro x 
    have hx : f x * f 1 - f (x * 1) = x + 1 := h x 1 
    have hx2 : f (x * 1) = f x := by 
        simp 
    rw [hx2] at hx 
    rw [h2] at hx 
    linarith 
  · -- Assume f(x) = x + 1 for all x 
    intro hf x y 
    have hfx : f x = x + 1 := hf x 
    have hfy : f y = y + 1 := hf y 
    have hfxy : f (x * y) = x * y + 1 := by 
      have h4 : f (x * y) = x * y + 1 := by 
        specialize hf (x * y) 
        simpa using hf 
      linarith 
    rw [hfx, hfy, hfxy] 
    ring