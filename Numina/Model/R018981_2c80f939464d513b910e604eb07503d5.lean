import Mathlib

theorem algebra_201720 (ω φ : ℝ) (hω : ω > 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.sin (ω * x + φ)) (h : ∀ x, f x = f (x + 1) - f (x + 2))
    (A B : ℝ → ℝ) (hA : A = fun x => Real.sin (ω * x + φ + 9 * ω)) (hB : B = fun x => Real.sin (ω * x + φ - 9 * ω)) :
    A = B := by
  have eq1 : ∀ x, f (x + 3) = -f x := by
    intro x 
    have eq2 := h x
    have eq3 := h (x + 1)
    have eq4 := h (x + 2)
    simp [hf] at eq2 eq3 eq4
    simp [hf]
    all_goals
      ring_nf at eq2 eq3 eq4 ⊢
      <;> nlinarith [Real.sin_sq_add_cos_sq (ω * x + φ), Real.sin_sq_add_cos_sq (ω * (x + 1) + φ), Real.sin_sq_add_cos_sq (ω * (x + 2) + φ), Real.sin_sq_add_cos_sq (ω * (x + 3) + φ)]
  have eq2 : ∀ x, f (x + 6) = f x := by
    intro x
    have eq3 := eq1 x
    have eq4 := eq1 (x + 3)
    rw [show x + 3 + 3 = x + 6 by ring] at eq4
    have eq5 : f (x + 6) = -f (x + 3) := by linarith [eq4]
    have eq6 : f (x + 3) = -f x := by linarith [eq3]
    rw [eq6] at eq5
    have eq7 : f (x + 6) = f x := by linarith [eq5]
    linarith
  funext x 
  have h_eq1 : A x = f (x + 9) := by 
    rw [hA]
    simp [hf]
    <;> ring_nf <;> simp [hf] <;> ring_nf <;> simp [hf]
  have h_eq2 : B x = f (x - 9) := by 
    rw [hB]
    simp [hf]
    <;> ring_nf <;> simp [hf] <;> ring_nf <;> simp [hf]
  have eq3 : f (x + 9) = -f x := by 
    have eq4 : f (x + 9) = -f (x + 6) := by 
      specialize eq1 (x + 6)
      rw [show x + 6 + 3 = x + 9 by ring] at eq1 
      linarith 
    have eq5 : f (x + 6) = f x := by 
      apply eq2 x 
    rw [eq5] at eq4 
    linarith 
  have eq4 : f (x - 9) = -f x := by
    have eq5 : f (x - 6) = f x := by 
      specialize eq2 (x - 6)
      rw [show x - 6 + 6 = x by ring] at eq2
      linarith 
    have eq6 : f (x - 3) = -f (x - 6) := by 
      specialize eq1 (x - 6)
      rw [show x - 6 + 3 = x - 3 by ring] at eq1 
      linarith 
    have eq7 : f (x - 3) = -f x := by 
      rw [eq5] at eq6 
      linarith 
    have eq8 : f (x - 9) = -f (x - 6) := by 
      specialize eq1 (x - 9)
      rw [show x - 9 + 3 = x - 6 by ring] at eq1 
      linarith 
    rw [eq5] at eq8 
    linarith 
  have h_eq3 : A x = B x := by 
    rw [h_eq1, h_eq2] 
    linarith [eq3, eq4] 
  simpa using h_eq3