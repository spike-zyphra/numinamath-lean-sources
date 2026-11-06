import Mathlib

theorem algebra_126867 (f : ℝ → ℝ) (hf : StrictMono f)
    (h : ∀ x y, f (f x + y) = f (x + y) + f 0) :
    ∃ c, ∀ x, f x = x + c := by
  use f 0
  intro x
  have h1 := h 0 0
  norm_num at h1
  have h2 : ∀ y, f (f 0 + y) = f y + f 0 := by
    intro y
    specialize h 0 y
    simpa using h
  have h3 := h2 (-f 0)
  have h4 : f (-f 0) = 0 := by
    norm_num at h3 ⊢
    all_goals linarith
  have h6 : ∀ x, f (x - f x) = 0 := by
    intro x
    have h7 : f (f x + (-f x)) = f (x + (-f x)) + f 0 := by
      specialize h x (-f x)
      simpa using h
    have h8 : f (f x + (-f x)) = f 0 := by
      have h9 : f x + (-f x) = (0 : ℝ) := by
        nlinarith
      have eq1 : f (f x + (-f x)) = f 0 := by
        rw [show f x + (-f x) = (0 : ℝ) by nlinarith]
        all_goals linarith 
      exact eq1
    have eq1 : f (x + -f x) = 0 := by
      linarith [h7, h8] 
    have h10 : x - f x = x + -f x := by
      ring
    rw [h10]
    exact eq1
  have h7 : ∀ x, f x = x + f 0 := by
    intro x
    have h8 := h6 x
    have h9 : x - f x = -f 0 := by
      have h10 : f (x - f x) = (0 : ℝ) := by
        simpa using h8
      have h11 : f (-f 0) = (0 : ℝ) := h4
      have h12 : x - f x = -f 0 := by
        by_cases h13 : x - f x < -f 0
        · have h14 : f (x - f x) < f (-f 0) := by
            apply hf.lt_iff_lt.mpr
            linarith
          rw [h10, h11] at h14
          all_goals linarith
        by_cases h13 : x - f x > -f 0
        · have h14 : f (x - f x) > f (-f 0) := by
            apply hf.lt_iff_lt.mpr
            linarith
          rw [h10, h11] at h14
          all_goals linarith
        · -- cases where x - f x = -f 0
          linarith
      linarith
    linarith [h9]
  exact h7 x
  all_goals nlinarith
  all_goals linarith
  all_goals linarith