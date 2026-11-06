import Mathlib

theorem algebra_293229 (l w h : ℝ) (h₀ : l * w * h = 8) (h₁ : 2*(l*w + w*h + l*h) = 32)
    (h₂ : ∃ r, w = l * r ∧ h = w * r) :
    4*(l + w + h) = 32 := by
  rcases h₂ with ⟨r, hw, hh⟩
  have hw_eq : w = l * r := hw
  have hh_eq : h = l * r ^ 2 := by
    rw [hh]
    rw [hw_eq]
    <;> ring
  -- Substitute w and h in the volume equation 
  have h3 : (l * r) ^ 3 = 8 := by 
    rw [hw_eq, hh_eq] at h₀ 
    nlinarith 
  -- Solving (l * r) ^ 3 = 8 to get l * r = 2
  have h4 : l * r = 2 := by
    have h5 : (l * r) ^ 3 - 8 = 0 := by linarith
    have h6 : (l * r - 2) * ((l * r) ^ 2 + 2 * (l * r) + 4) = 0 := by
      ring_nf at h5 ⊢ 
      linarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case where l * r - 2 = 0 
      linarith 
    · -- Case where (l * r) ^ 2 + 2 * (l * r) + 4 = 0 
      nlinarith [sq_nonneg ((l * r) + 1)]
  -- From hw_eq and h4, we have w = 2
  have hw2 : w = 2 := by 
    nlinarith [hw_eq, h4]
  -- From h₀ and hw2, we can calculate l * h
  have h8 : l * h = 4 := by
    rw [hw2] at h₀ 
    nlinarith
  -- From h₁, we can derive l * w + w * h + l * h = 16 
  have h9 : l * w + w * h + l * h = 16 := by 
    linarith 
  -- Substitute w = 2 and l * h = 4 into h9 to find l + h 
  rw [hw2] at h9 
  have h10 : l + h = 6 := by 
    nlinarith [h8]
  -- Calculate l + w + h 
  have h11 : l + w + h = 8 := by 
    nlinarith [hw2, h10]
  -- Calculate 4*(l + w + h)
  linarith [h11]