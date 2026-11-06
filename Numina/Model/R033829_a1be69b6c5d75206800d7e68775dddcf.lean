import Mathlib

theorem algebra_228718 (f : ℝ → ℝ) (h₁ : ∀ x, f (x + 3) ≤ f x + 3) (h₂ : ∀ x, f (x + 2) ≥ f x + 2)
    (h₃ : f 1 = 2) : f 2015 = 2016 := by
  have h1 x : f x + 3 ≥ f (x + 1) + 2 := calc
    f x + 3 ≥ f (x + 3) := h₁ x
    _ = f (x + 1 + 2) := by ring_nf
    _ ≥ f (x + 1) + 2 := h₂ (x + 1)

  have h2 x : f x + 4 ≤ f (x + 1) + 3 := calc
    f x + 4 = (f x + 2) + 2 := by ring
    _ ≤ f (x + 2) + 2 := by gcongr; exact h₂ _
    _ ≤ f (x + 2 + 2) := h₂ (x + 2)
    _ = f (x + 1 + 3) := by ring_nf
    _ ≤ f (x + 1) + 3 := h₁ (x + 1)

  have h3 x : f (x + 1) = f x + 1 := by
    have h8 : f (x + 1) ≤ f x + 1 := by
      linarith [h1 x]
    have h9 : f (x + 1) ≥ f x + 1 := by
      linarith [h2 x]
    linarith

  have h4 : ∀ (n : ℕ), f (1 + (↑n : ℝ)) = 2 + (↑n : ℝ) := by
    intro n
    induction n with
    | zero =>
      norm_num
      all_goals
      try { linarith [h₃] }
    | succ n ih =>
      have eq1 : f (1 + ((↑(n + 1) : ℝ)) ) = f ( (1 + (↑n : ℝ)) + 1 ) := by
        simp at *
        all_goals ring_nf
      rw [eq1]
      have eq2 : f ( (1 + (↑n : ℝ)) + 1 ) = f (1 + (↑n : ℝ)) + 1 := by
        specialize h3 (1 + (↑n : ℝ))
        linarith [h3]
      rw [eq2, ih]
      all_goals simp
      all_goals linarith

  specialize h4 2014
  norm_num at h4 ⊢
  all_goals
  try { linarith }