import Mathlib

theorem algebra_217552 (f : ℝ → ℝ) :
    (∀ x y, f (f x + f y) = f x + y) ↔ ∀ x, f x = x := by
  constructor
  · -- Assume the functional equation holds, prove f x = x
    intro h
    have injective_f : Function.Injective f := by
      intro a b hfx
      have h1 := h 0 a
      have h2 := h 0 b
      simp [hfx] at h1 h2
      linarith
    have surjective_f : Function.Surjective f := by
      intro c
      have h1 := h 0 (c - f 0)
      have h_eq : f (f 0 + f (c - f 0)) = c := by
        have eq1 : f 0 + (c - f 0) = c := by
          linarith
        have eq2 : f (f 0 + f (c - f 0)) = f 0 + (c - f 0) := by 
          simpa using h1
        rw [eq1] at eq2
        linarith
      exact ⟨f 0 + f (c - f 0), h_eq⟩
    -- Now exists z0 s.t. f(z0) =0
    have exists_z0 : ∃ z0, f z0 = 0 := by 
      apply surjective_f
      all_goals norm_num
    rcases exists_z0 with ⟨z0, hz0⟩
    -- Now f z0 =0
    have h1 := h z0 z0
    simp [hz0] at h1
    -- Now f 0 = z0
    have h2 : ∀ y, f (f y) = y := by 
      intro y 
      have h3 := h z0 y
      simp [hz0] at h3 
      linarith 
    -- Now f(f y) = y
    have h3 : ∀ y, f (f y) = y := h2 
    -- Now f(f x) = x
    have h5 : ∀ x, f (f x) = x := h3 
    -- Now from the functional equation by setting y = z0
    have h6 : ∀ x, f (f x + f z0) = f x + z0 := by 
      intro x 
      specialize h x z0 
      simpa using h 
    -- Now we can show z0 =0
    have eq1 := h6 0 
    have h7 : f (f 0 + f z0) = f 0 + z0 := by 
      simpa using h6 0 
    have h8 : f 0 = z0 := by 
      linarith [h1]
    have h9 : f z0 = 0 := hz0 
    simp [h9, h8] at h7 
    have hz00 : z0 = 0 := by 
      linarith 
    have h10 : f 0 = 0 := by 
      rw [hz00] at h8 
      linarith 
    intro x 
    -- From functional equation x y, set y = z0 
    have hfxz0 : f (f x) = f x + z0 := by 
      specialize h6 x 
      simp [show f z0 = 0 by linarith [hz0]] at h6 ⊢
      linarith 
    have hfx0 : f (f x) = x := by 
      apply h5 x 
    have hfx_eq : f x = x - z0 := by 
      linarith [hfx0, hfxz0] 
    rw [show z0 = (0 : ℝ) by linarith [hz00]] at hfx_eq 
    linarith
  · -- Assume f x = x, prove the functional equation
    intro hf x y
    have hfx : f x = x := hf x
    have hfy : f y = y := hf y
    rw [show f x + f y = x + y by 
      linarith [hfx, hfy]
    ]
    have hxy : f (x + y) = x + y := by 
      have hx_eq : f (x + y) = x + y := by 
        simpa using hf (x + y)
      linarith 
    linarith [hxy, hfx]