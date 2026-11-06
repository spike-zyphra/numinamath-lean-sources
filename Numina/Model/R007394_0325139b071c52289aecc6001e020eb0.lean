import Mathlib

theorem algebra_220658 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hparabola : ∀ x, a * x ^ 2 + b * x + c > c * x) :
    ∀ x, c * x ^ 2 - b * x + a > c * x - b := by
  intro x
  have h1 : ∀ x, a * x ^ 2 + (b - c) * x + c > 0 := by
    intro x
    specialize hparabola x
    nlinarith
  have h2 : c > 0 := by
    specialize h1 0
    nlinarith
  have h3 : (b - c) ^ 2 - 4 * a * c < 0 := by 
    by_contra h
    push_neg at h
    have h4 : ∃ x : ℝ, a * x ^ 2 + (b - c) * x + c ≤ 0 := by 
      have h' : (b - c) ^ 2 - 4 * a * c ≥ 0 := by nlinarith
      have : ∃ x : ℝ, a * x ^ 2 + (b - c) * x + c = 0 := by 
        use ( - (b - c) - Real.sqrt ((b - c) ^ 2 - 4 * a * c) ) / (2 * a)
        field_simp [show a ≠ 0 by exact ha]
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        nlinarith
      obtain ⟨x, hx⟩ := this
      use x
      nlinarith
    obtain ⟨x, hx⟩ := h4
    linarith [h1 x, hx]
  
  have h5 : (b + c) ^ 2 - 4 * c * (a + b) < 0 := by
    nlinarith
  
  have h6 : c * x ^ 2 - (b + c) * x + (a + b) > 0 := by
    nlinarith [sq_nonneg (x - (b + c) / (2 * c)), h2, h5, sq_nonneg (c * x - (b + c) / 2), show c ≠ 0 by exact hc]

  nlinarith [h6]