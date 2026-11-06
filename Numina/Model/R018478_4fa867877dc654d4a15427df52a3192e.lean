import Mathlib


theorem algebra_140804 {f : ℝ → ℝ} (h : ∀ x, f (x + 1) = f (-x))
    (hf : ∀ x, x ∈ Set.Ioc (-1) 0 → f x = 1) (hf' : ∀ x, x ∈ Set.Ioc 0 1 → f x = -1) :
    f (f 3.5) = -1 := by
  have h1 : f 0 = 1 := by
    specialize hf 0 (by norm_num [Set.mem_Ioc])
    simpa using hf

  have h4 : f 1 = -1 := by
    specialize hf' 1 (by norm_num [Set.mem_Ioc])
    simpa using hf'

  -- Now with x = -1, applying the functional equation:
  -- f(-1 + 1) = f(-(-1))
  -- f(0) = f(1)
  -- So 1 = f(1).
  have h2 : f 1 = 1 := by
    have h10 : f 0 = 1 := h1
    have h0 : f 0 = f 1 := by
      specialize h (-1)
      norm_num at h ⊢
      all_goals
        linarith [h, h10]
    linarith [h0, h10]

  -- This contradicts with hf' which says f 1 = -1
  linarith [h2, h4]