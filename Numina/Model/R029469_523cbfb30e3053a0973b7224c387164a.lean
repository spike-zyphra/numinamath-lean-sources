import Mathlib

theorem algebra_112883 (f : ℝ → ℝ) (h : ∀ x y, f (2 * f x + f y) = 2 * x + f y) :
    ∀ x, f x = x := by
  have h1 : ∀ y, f (2 * f 0 + f y) = f y := by
    intro y 
    specialize h 0 y 
    simpa using h 
  have h_inj : ∀ a b, f a = f b → a = b := by
    intro a b hab
    have eq1 := h a (0 : ℝ)
    have eq2 := h b (0 : ℝ)
    simp [hab] at eq1 eq2
    linarith
  have h_eq : ∀ y, f y = y - 2 * f 0 := by
    intro y
    have eq1 := h1 y
    have eq2 : 2 * f 0 + f y = y := by
      have h_inj2 : ∀ a b, f a = f b → a = b := h_inj
      have eq4 : f (2 * f 0 + f y) = f y := by 
        simpa using eq1
      specialize h_inj2 (2 * f 0 + f y) y eq4
      linarith
    linarith
  have eq1 : ∀ x y, f (2 * f x + f y) = 2 * x + f y := h
  have eq2 : ∀ y, f y = y - 2 * f 0 := h_eq 
  have eq5 : f 0 = 0 := by 
    have eq111 := h 1 0 
    have eq112 := eq2 1 
    have eq311 := eq2 (2 * f 1 + f 0) 
    have eq41 : f (2 * f 1 + f 0) = 2 + f 0 := by 
      linarith 
    have eq42 : f (2 * f 1 + f 0) = (2 * f 1 + f 0) - 2 * f 0 := by 
      specialize eq2 (2 * f 1 + f 0) 
      linarith 
    have eq43 : f 1 = 1 - 2 * f 0 := by 
      specialize eq2 1 
      linarith 
    rw [eq42] at eq41
    rw [eq43] at eq41 
    linarith 
  intro x 
  have eq6 := eq2 x 
  rw [eq5] at eq6 
  linarith