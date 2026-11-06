import Mathlib

theorem algebra_289267 (a b c : ℝ) (h₀ : a^2 + b^2 + c^2 = 26) (h₁ : a + b = 5) (h₂ : b + c ≥ 7) :
    a = 1 ∧ b = 4 ∧ c = 3 := by
  have h3 : a = 5 - b := by linarith
  rw [h3] at h₀
  have h4 : 2 * b ^ 2 - 10 * b + c ^ 2 = 1 := by
    ring_nf at h₀
    linarith
  have h5 : c ≥ 7 - b := by linarith
  have h6 : (b - 4) ^ 2 = 0 := by
    nlinarith [sq_nonneg (c - 3), sq_nonneg (a - 1), sq_nonneg (b - 4)]
  have hb : b = 4 := by
    nlinarith 
  have hc : c = 3 := by 
    rw [hb] at h4
    nlinarith [sq_nonneg c]
  have ha : a = 1 := by
    rw [hb] at h3
    linarith
  exact ⟨ha, hb, hc⟩