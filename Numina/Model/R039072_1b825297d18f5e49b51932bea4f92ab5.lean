import Mathlib

theorem algebra_10573 (f g : ℝ → ℝ)
    (hf : f = fun x => abs (2 * x + 5)) (hg : g = fun x => -abs (3 * x - 2)) :
    {x | f x = g x} = ∅ := by
  have h1 : ∀ x, f x ≠ g x := by 
    intro x
    have hfx : f x = abs (2 * x + 5) := by 
      rw [hf]
    have hgx : g x = -abs (3 * x - 2) := by 
      rw [hg]
    intro h
    rw [hfx] at h 
    rw [hgx] at h 
    have h2 : abs (2 * x + 5) ≥ 0 := abs_nonneg (2 * x + 5)
    have h3 : -abs (3 * x - 2) ≤ 0 := by 
      have h4 : abs (3 * x - 2) ≥ 0 := abs_nonneg (3 * x - 2)
      linarith 
    have h4 : abs (2 * x + 5) = 0 := by linarith 
    have h5 : abs (3 * x - 2) = 0 := by 
      linarith [abs_nonneg (3 * x - 2), abs_nonneg (2 * x + 5), h4] 
    have h6 : 2 * x + 5 = 0 := by 
      rwa [abs_eq_zero] at h4 
    have h7 : 3 * x - 2 = 0 := by 
      rwa [abs_eq_zero] at h5 
    have h8 : x = (-5 : ℝ) / 2 := by 
      linarith 
    have h9 : x = (2 : ℝ) / 3 := by 
      linarith 
    linarith 
  have h2 : {x | f x = g x} = ∅ := by 
    ext x 
    simp [h1 x] 
  exact h2