import Mathlib

theorem algebra_193313 :
    {f : ℝ → ℝ | ∀ x y, 2 * f (x + y) + f (x - y) = f x * (2 * Real.exp y + Real.exp (-y))} = {f : ℝ → ℝ | ∃ c, ∀ x, f x = c * Real.exp x} := by
  ext f 
  simp only [Set.mem_setOf_eq]
  constructor 
  · -- First: if f satisfies functional equation then it is exponential
    intro h 
    have h1 : ∀ y, 2 * f y + f (-y) = f 0 * (2 * Real.exp y + Real.exp (-y)) := by
      intro y 
      specialize h 0 y
      norm_num at h ⊢
      simpa using h
    have h2 : ∀ y, 2 * f (-y) + f y = f 0 * (2 * Real.exp (-y) + Real.exp y) := by
      intro y 
      specialize h1 (-y)
      rw [show -(-y) = y by ring] at h1
      simpa using h1
    have h3 : ∀ y : ℝ, f y = f 0 * Real.exp y := by 
      intro y 
      have eq1 := h1 y 
      have eq2 := h2 y 
      have eq3 : f (-y) = f 0 * (2 * Real.exp y + Real.exp (-y)) - 2 * f y := by 
        linarith
      rw [eq3] at eq2 
      have eq4 : f y = f 0 * Real.exp y := by 
        have h6 : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y 
        simp [h6] at eq1 eq2 
        have h7 : Real.exp y ≠ 0 := by positivity 
        nlinarith [Real.exp_pos y, Real.exp_pos (-y), Real.mul_self_sqrt (show (0 : ℝ) ≤ Real.exp y by positivity), Real.sqrt_nonneg (Real.exp y), Real.exp_pos (0 : ℝ)]
      exact eq4 
    have hf : ∃ c, ∀ x, f x = c * Real.exp x := by 
      refine ⟨f 0, fun x => by 
        have hx : f x = f 0 * Real.exp x := by 
          specialize h3 x
          simpa using h3 
        simpa using hx 
      ⟩
    tauto 
  · -- Show the converse
    rintro ⟨c, hc⟩
    intro x y 
    have eq1 : f (x + y) = c * Real.exp (x + y) := by
      specialize hc (x + y)
      simpa using hc 
    have eq2 : f (x - y) = c * Real.exp (x - y) := by 
      specialize hc (x - y)
      simpa using hc 
    have eq3 : f x = c * Real.exp x := by 
      specialize hc x 
      simpa using hc 
    rw [eq1, eq2, eq3]
    have eq4 : Real.exp (x + y) = Real.exp x * Real.exp y := Real.exp_add x y
    have eq5 : Real.exp (x - y) = Real.exp x * Real.exp (-y) := by 
      rw [show x - y = x + (-y) by ring]
      rw [Real.exp_add x (-y)]
    rw [eq4, eq5]
    simp [Real.exp_neg] at *
    all_goals ring_nf