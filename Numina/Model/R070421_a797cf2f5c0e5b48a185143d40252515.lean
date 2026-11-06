import Mathlib

theorem algebra_5172 {f : ℝ → ℝ} (h : Function.Injective f)
  (h1 : ∀ x y, f (x * y) = f x * f y) (h2 : ∀ x y, f (x + y) = f x + f y) :
  ∀ x y, x < y → f x < f y := by
  
  have h3 : f 0 = 0 := by
    have h4 := h2 0 0
    simp at h4
    linarith
  
  have h4 : f 1 = 1 := by
    have h5 := h1 1 1
    simp at h5
    have h6 : f 1 * (f 1 - 1) = 0 := by 
      linarith 
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case where f 1 = 0
      have h9 : f 1 = f 0 := by 
        linarith [h3, h7]
      have h10 : (1 : ℝ) = (0 : ℝ) := by 
        exact h h9
      linarith 
    · -- Case where f 1 - 1 = 0
      linarith
  
  have h5 : ∀ x, f (-x) = - f x := by
    intro x 
    have h6 := h2 x (-x)
    simp [h3] at h6 
    have h7 : f (-x) = - f x := by linarith 
    exact h7
  
  have h6 : ∀ x > 0, f x > 0 := by 
    intro x hx
    have h7 : ∃ s > 0, s ^ 2 = x := by 
      use Real.sqrt x 
      constructor 
      · -- Show that sqrt x > 0 when x > 0
        positivity 
      · -- Show that (sqrt x) ^ 2 = x when x > 0
        rw [Real.sq_sqrt]
        linarith 
    rcases h7 with ⟨s, hs, h8⟩ 
    have h9 := h1 s s 
    rw [show s * s = x by linarith [h8]] at h9 
    have h10 : f x = (f s) ^ 2 := by 
      linarith 
    have h11 : f s ≠ 0 := by 
      by_contra h12 
      have h13 : f s = f 0 := by 
        linarith [h3, h12] 
      have h14 : s = (0 : ℝ) := by 
        exact h h13 
      linarith [hs, h14] 
    have h15 : (f s) ^ 2 > 0 := by 
      exact sq_pos_of_ne_zero h11 
    linarith [h10, h15]
  
  intro x y hxy 
  have h8 : y - x > 0 := by linarith 
  have h9 : f (y - x) > 0 := h6 (y - x) h8 
  have h10 : f y = f x + f (y - x) := by 
    specialize h2 x (y - x) 
    have : x + (y - x) = y := by ring 
    rw [this] at h2 
    linarith 
  linarith [h10, h9]