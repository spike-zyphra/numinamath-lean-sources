import Mathlib

theorem algebra_252959 (f : ℝ → ℝ) :
    (∀ x y, f (f (x * y)) = x * f y + 3 * f (x * y)) ↔
    (∀ x, f x = 0) ∨ (∀ x, f x = 4 * x) := by

  constructor 
  · -- Assume the functional equation, prove the disjunction of solutions 
    intro h 
    have h1 : f (f (0)) = 3 * (f 0) := by 
      specialize h 0 0 
      simp at h 
      linarith 
    -- Substituting y = 0
    have h3 : ∀ x : ℝ, f (f 0) = x * f 0 + 3 * f 0 := by 
      intro x 
      specialize h x 0 
      simp at h 
      linarith 
    -- Prove f(0) = 0 
    have hf0 : f 0 = 0 := by 
      have eq1 := h3 0 
      have eq2 := h3 1 
      linarith 
    -- Substituting x = 1 
    have h4 : ∀ y : ℝ, f (f y) = 4 * f y := by 
      intro y 
      specialize h 1 y 
      simp at h 
      linarith 
    -- Prove f(x * y) = x * f(y) 
    have h5 : ∀ x y : ℝ, f (x * y) = x * f y := by 
      intro x y 
      have eq1 := h x y 
      have eq2 := h4 (x * y) 
      simp at eq1 eq2 
      linarith 
    -- Prove f(x) = x * f(1) 
    have h6 : ∀ x : ℝ, f x = x * f 1 := by 
      intro x 
      specialize h5 x 1 
      simp at h5 
      linarith 
    -- Determine f(1) 
    have h7 : f (f 1) = 4 * f 1 := h4 1 
    have h8 : f (f 1) = (f 1) * (f 1) := by 
      specialize h6 (f 1) 
      linarith 
    have h9 : (f 1) * (f 1) = 4 * (f 1) := by 
      linarith [h7, h8] 
    -- Solve the equation 
    have h10 : f 1 * (f 1 - 4) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h10) with h11 h12 
    · -- f 1 = 0 
      have h13 : ∀ x, f x = 0 := by 
        intro x 
        specialize h6 x 
        rw [h11] at h6 
        linarith 
      left 
      exact h13 
    · -- f 1 - 4 = 0 
      have h14 : f 1 = 4 := by linarith 
      have h15 : ∀ x, f x = 4 * x := by 
        intro x 
        specialize h6 x 
        rw [h14] at h6 
        linarith 
      right 
      exact h15 
  · -- Show that the solutions satisfy the functional equation 
    rintro (h | h) 
    · -- ∀ x, f x = 0 
      intro x y 
      simp [h] 
    · -- ∀ x, f x = 4 * x 
      intro x y 
      simp [h] 
      <;> ring_nf <;> simp [h] <;> ring