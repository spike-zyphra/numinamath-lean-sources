import Mathlib

theorem algebra_257572 {f : ℝ → ℝ} (h : ∀ x y, f (f (x * y)) = abs x * f y + 3 * f (x * y)) :
    ∀ x, f x = 0 ∨ f x = 4 * abs x ∨ f x = -4 * abs x := by

  have h1 : f (f 0) = 3 * f 0 := by
    specialize h 0 0
    simp at h 
    linarith
  have h2 : f 0 = 0 := by
    specialize h 1 0
    norm_num [h1] at h
    all_goals linarith

  have h3 : ∀ y : ℝ, f (f y) = 4 * f y := by
    intro y
    specialize h 1 y
    norm_num at h 
    linarith

  have h4 : ∀ x : ℝ, f x = f 1 * abs x := by 
    intro x
    have eq1 : f (f x) = 4 * f x := h3 x
    have eq2 : f (f x) = abs x * f 1 + 3 * f x := by
      specialize h x 1 
      simpa using h
    have eq3 : f x = f 1 * abs x := by
      nlinarith [eq1, eq2]
    exact eq3

  have h5 : f 1 * abs (f 1) = 4 * f 1 := by
    have eq1 : f (f 1) = 4 * f 1 := h3 1
    have eq2 : f (f 1) = f 1 * abs (f 1) := by
      specialize h4 (f 1)
      simpa using h4
    linarith [eq1, eq2]

  have h6 : f 1 = 0 ∨ f 1 = 4 ∨ f 1 = -4 := by
    by_cases h7 : f 1 = 0
    · -- f 1 = 0
      left
      exact h7
    · -- f 1 ≠ 0
      have h8 : abs (f 1) = 4 := by
        have h9 : f 1 ≠ 0 := h7
        apply (mul_left_inj' h9).mp 
        linarith [h5]
      have h10 : f 1 = 4 ∨ f 1 = -4 := by 
        cases' eq_or_eq_neg_of_abs_eq h8 with h11 h12
        · -- f 1 = 4
          left
          linarith
        · -- f 1 = -4
          right
          linarith
      tauto

  intro x
  rcases h6 with (h7 | h7 | h7)
  · -- f 1 = 0 
    have hx0 : f x = 0 := by 
      specialize h4 x 
      rw [h7] at h4 
      norm_num at h4 ⊢ 
      <;> linarith 
    left 
    exact hx0
  · -- f 1 = 4
    have hx1 : f x = 4 * abs x := by 
      specialize h4 x 
      rw [h7] at h4 
      linarith 
    right 
    left 
    exact hx1 
  · -- f 1 = -4 
    have hx2 : f x = -4 * abs x := by 
      specialize h4 x 
      rw [h7] at h4 
      linarith 
    right 
    right 
    exact hx2