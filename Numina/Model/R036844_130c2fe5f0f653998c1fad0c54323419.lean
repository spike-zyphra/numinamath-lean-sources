import Mathlib

theorem algebra_117295 (f : ℝ → ℝ) (h : ∀ x y, f (f (x + 1) + y - 1) = f x + y) :
    ∀ y, f y = y := by
  have surj : ∀ t, ∃ z, f z = t := by
    intro t
    use f (1) + (t - f 0) - 1
    have eq1 := h 0 (t - f 0)
    norm_num at eq1
    linarith [eq1]

  have h1 : ∀ x, f (f (x + 1)) = f x + 1 := by
    intro x 
    specialize h x 1
    norm_num at h 
    linarith

  have h2 : ∀ z, f z = z + (f (-1) + 1 - f 0) := by
    intro z 
    have eq1 := h (-1) (z - f 0 + 1)
    have eq2 : f (f (-1 + 1) + (z - f 0 + 1) - 1) = f (-1) + (z - f 0 + 1) := by 
      simpa using eq1 
    have eq3 : f (-1 + 1) = f 0 := by 
      norm_num 
    have eq4 : f (f (-1 + 1) + (z - f 0 + 1) - 1) = f z := by
      rw [eq3]
      ring_nf 
    rw [eq4] at eq2 
    linarith

  have h4 : f (-1) + 1 - f 0 = 0 := by 
    have eq1 : ∀ x, f (f (x + 1)) = f (x + 1) + (f (-1) + 1 - f 0) := by
      intro x 
      have eq2 : f (f (x + 1)) = f (x + 1) + (f (-1) + 1 - f 0) := by 
        specialize h2 (f (x + 1))
        linarith 
      linarith
    have eq2 : ∀ x, f (f (x + 1)) = f x + 1 := h1 
    have eq4 : ∀ x, f x = x + (f (-1) + 1 - f 0) := by 
      intro x
      specialize h2 x 
      linarith 
    have eq5 : ∀ x, f (x + 1) = (x + 1) + (f (-1) + 1 - f 0) := by 
      intro x 
      have eq6 : f (x + 1) = (x + 1) + (f (-1) + 1 - f 0) := by 
        specialize h2 (x + 1)
        linarith 
      linarith 

    have eq3a := eq1 0 
    have eq3b := eq2 0 
    have eq3c := eq4 0 
    have eq3d := eq4 1 
    have eq3e := eq5 0 
    norm_num at eq3a eq3b eq3c eq3d eq3e 
    all_goals 
      linarith 

  intro y 
  have eq1 : f y = y + (f (-1) + 1 - f 0) := by 
    specialize h2 y 
    linarith 
  rw [eq1]
  rw [h4]
  all_goals norm_num