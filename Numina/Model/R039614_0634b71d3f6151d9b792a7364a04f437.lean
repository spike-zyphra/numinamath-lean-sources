import Mathlib

theorem algebra_311003 (k m : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x y, f (x * f y) = k * x * y + x + m) :
    m ≠ 0 ∧ k = 1 / m ^ 2 ∧ ∀ x, f x = x / m + m := by
  have h1 : f 0 = m := by
    specialize h₀ 0 0
    norm_num at h₀ 
    linarith 
  -- Substitute y = 0 into the functional equation: f(x * m) = x + m
  have h2 : ∀ x : ℝ, f (x * m) = x + m := by
    intro x 
    specialize h₀ x 0 
    rw [show f 0 = m by linarith [h1]] at h₀ 
    simp at h₀ 
    linarith 
  have hm : m ≠ 0 := by
    by_contra h
    have h4 : m = 0 := by linarith 
    have h4 : m = 0 := by linarith 
    -- Show contradiction if m = 0 
    have h5 : ∀ x : ℝ, f (x * 0) = x + 0 := by 
      intro x 
      specialize h2 x 
      rw [h4] at h2 
      simpa using h2 
    -- Show f 0 = 0 from h1
    have h6 : f 0 = 0 := by 
      rw [h1] 
      all_goals linarith 
    -- Contradiction by f 0 = x 
    have h7 : f (1 * 0) = 1 + 0 := h5 1 
    -- Simplify h7 and h6 
    norm_num at h7 
    all_goals linarith [h6, h7] 
  have hf : ∀ x : ℝ, f x = x / m + m := by
    intro x 
    have h4 : f ( (x / m) * m ) = (x / m) + m := by 
      specialize h2 (x / m) 
      simpa using h2 
    have h5 : (x / m) * m = x := by 
      field_simp [hm] 
    rw [h5] at h4 
    linarith 
  -- Compute `k` from the functional equation 
  have hk : k = 1 / m ^ 2 := by
    have eq1 := h₀ 1 1
    simp at eq1 
    have hf1 : f 1 = 1 / m + m := by
      specialize hf 1 
      simpa using hf 
    have eq2 : f (f 1) = (1 / m + m) / m + m := by
      rw [hf1]
      have eq3 : f ( (1 / m + m) ) = ( (1 / m + m) / m ) + m := by
        specialize hf (1 / m + m) 
        linarith [hf] 
      linarith [eq3]
    rw [eq2] at eq1 
    field_simp [hm] at eq1 ⊢ 
    nlinarith [sq_pos_of_ne_zero (show m ≠ 0 by assumption)]
  constructor 
  · exact hm 
  constructor 
  · exact hk 
  · intro x 
    exact hf x