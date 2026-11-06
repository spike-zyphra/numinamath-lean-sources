import Mathlib

theorem number_theory_272610 (s t : ℤ) (h₀ : s > 0) (h₁ : t > 0)
    (h₂ : s * (s - t) = 29) : s + t = 57 := by
  have h3 : s ∣ 29 := by 
    use s - t
    linarith
  have h4 : s = 1 ∨ s = 29 := by 
    have h5 : s ≤ 29 := by 
      apply Int.le_of_dvd (by norm_num) h3
    interval_cases s <;> tauto
  cases h4 with
  | inl h1 =>
    have h6 : s - t = 29 := by
      rw [h1] at h₂
      have : (1 : ℤ) * (1 - t) = 29 := by linarith 
      linarith
    have h9 : t < 0 := by 
      linarith [h6, h1]
    linarith
  | inr h2 =>
    have h10 : s - t = 1 := by 
      rw [h2] at h₂
      have : (29 : ℤ) * (29 - t) = 29 := by linarith 
      have : 29 - t = 1 := by 
        linarith 
      linarith 
    have ht : t = 28 := by 
      linarith [h2, h10]
    linarith [h2, ht]