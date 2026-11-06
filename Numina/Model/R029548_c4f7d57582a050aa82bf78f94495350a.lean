import Mathlib

theorem algebra_170376 (a b : ℝ) (h : {x : ℝ | Real.sin x + a = b * x ∧ Real.cos x = b}.encard = 2) :
    ∃ x, Real.sin x + a = b * x ∧ Real.cos x = b := by

  have h1 : {x : ℝ | Real.sin x + a = b * x ∧ Real.cos x = b}.Nonempty := by 
    by_contra h1
    push_neg at h1 
    have h2 : {x : ℝ | Real.sin x + a = b * x ∧ Real.cos x = b} = ∅ := by 
      ext x
      simp [h1] 
    rw [h2] at h
    simp at h 
  rcases h1 with ⟨x, hx⟩
  exact ⟨x, hx⟩