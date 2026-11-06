import Mathlib

theorem algebra_114681 {f : ℝ → ℝ} (hf : StrictMono f)
    (h : ∀ x y, f (x * f y) = f x * y) :
    ∀ x, f x = x := by
  have h1 : f 0 = 0 := by
    have h00 := h 0 0
    norm_num at h00
    all_goals linarith [h00]
  have h2 : ∀ x, f (x * f 1) = f x := by
    intro x
    specialize h x 1
    norm_num at h
    linarith
  have h6 : ∀ x, x * f 1 = x := by
    intro x
    have h7 : f (x * f 1) = f x := h2 x
    have h8 : x * f 1 = x := by
      apply hf.injective
      linarith [h7]
    exact h8
  have h4 : f 1 = 1 := by
    have h7 := h6 1
    norm_num at h7
    linarith
  have h5 : ∀ y, f (f y) = y := by
    intro y
    specialize h 1 y
    norm_num [h4] at h
    linarith
  intro x
  have h7 : f (f x) = x := h5 x
  by_cases h8 : f x > x
  · -- Assume f x > x
    have h9 : f (f x) > f x := by
      apply hf.lt_iff_lt.mpr
      all_goals linarith [h8]
    linarith [h7, h9, h8]
  · -- Assume f x ≤ x
    by_cases h9 : f x < x
    · -- Assume f x < x
      have h10 : f (f x) < f x := by
        apply hf.lt_iff_lt.mpr
        all_goals linarith [h9]
      linarith [h7, h10, h9]
    · -- Assume f x = x
      linarith [h9]