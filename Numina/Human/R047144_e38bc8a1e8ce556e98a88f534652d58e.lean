import Mathlib
/- Do there exist? functions f: ℝ → ℝ, such that f is surjective and f(f(x))=(x-1)f(x)+2 for all x real-/
theorem algebra_123753 : ¬∃ f : ℝ → ℝ, Function.Surjective f ∧ ∀ x, f (f x) = (x - 1) * f x + 2 := by
  intro h
  rcases h with ⟨f, hsurj, hf_eq⟩
  -- prove by evaluating on particular points 
  have h1 : f 0 = 2 := by
    have h0 := hf_eq 0
    have h2 := hf_eq (0)
    have hzero : ∃ x0, f x0 = 0 := by 
      apply hsurj 0
    rcases hzero with ⟨x0, hx0⟩
    have eq1 := hf_eq x0
    simp [hx0] at eq1
    linarith
  
  have h2 : f 2 = 0 := by
    have eq1 := hf_eq 0
    rw [h1] at eq1
    norm_num at eq1
    linarith
  
  have h3 : f 1 = 0 := by 
    have eq1 := hf_eq 1
    have h4 : ∀ y, f y = 2 → y = 0 := by 
      intro y hy
      have eq1 := hf_eq y
      rw [hy] at eq1
      have h2_eq : f 2 = 0 := h2
      have h5 : f 2 = (y - 1) * 2 + 2 := by linarith
      rw [h2_eq] at h5
      have h6 : y = 0 := by linarith
      exact h6
    have hff1 : f (f 1) = 2 := by
      specialize hf_eq 1
      norm_num at hf_eq
      linarith
    have h7 : f 1 = 0 := by 
      specialize h4 (f 1) hff1
      linarith
    exact h7
  
  have h4 : f (-1) = 1 := by 
    have h1_eq := hf_eq (-1)
    have h1_eq1 : ∃ y, f y = 1 := by 
      apply hsurj 1
    rcases h1_eq1 with ⟨y, hy⟩
    have hy_eq : f y = 1 := hy
    have eq1 := hf_eq y
    rw [hy_eq] at eq1
    rw [h3] at eq1
    have hy_eq2 : y = -1 := by
      norm_num at eq1
      linarith
    rw [hy_eq2] at hy_eq
    linarith
  
  have h5 : ∃ x, f x = -1 := by 
    apply hsurj (-1)
  rcases h5 with ⟨x', hx'⟩
  
  have eq2 := hf_eq x'
  rw [hx'] at eq2
  have h4_eq : f (-1) = 1 := h4
  rw [h4_eq] at eq2
  have h2_eq : f 2 = 0 := h2
  norm_num at eq2
  have hx_eq : x' = 2 := by linarith
  
  rw [hx_eq] at hx'
  linarith [h2_eq, hx']