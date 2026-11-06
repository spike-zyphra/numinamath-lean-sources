import Mathlib

theorem algebra_11342 {b c : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + b * x + c)
    (h : ¬∃ x : ℝ, f x = x) :
    ¬∃ x : ℝ, f (f x) = x := by
  intro h1
  rcases h1 with ⟨x, hx⟩
  have h2 : f (f x) = x := hx
  have h3 : (x ^ 2 + (b - 1) * x + c) + (f x ^ 2 + (b - 1) * f x + c) = 0 := by
    have eq1 : f x = x ^ 2 + b * x + c := hf x
    have eq2 : f (f x) = (f x)^2 + b * (f x) + c := hf (f x)
    rw [eq2] at h2
    nlinarith
  have h4 : ∀ x : ℝ, x ^ 2 + (b - 1) * x + c > 0 := by
    intro x
    by_contra h5
    push_neg at h5
    have h7 : ∃ y : ℝ, y ^ 2 + (b - 1) * y + c = 0 := by
      have h7 : (b - 1) ^ 2 - 4 * c ≥ 0 := by
        nlinarith [sq_nonneg (x + (b - 1) / 2)]
      have h9 : ∃ y : ℝ, y ^ 2 + (b - 1) * y + c = 0 := by
        have h10 : (b - 1) ^ 2 - 4 * c ≥ 0 := by
          nlinarith [sq_nonneg (x + (b - 1) / 2)]
        use (- (b - 1) + Real.sqrt ((b - 1) ^ 2 - 4 * c)) / 2
        nlinarith [Real.sqrt_nonneg ((b - 1) ^ 2 - 4 * c), Real.sq_sqrt (show ((b - 1) ^ 2 - 4 * c) ≥ 0 by linarith)]
      exact h9
    rcases h7 with ⟨y, hy⟩
    have h10 : f y = y := by
      rw [hf y]
      nlinarith
    have h11 : ∃ y : ℝ, f y = y := ⟨y, h10⟩
    contradiction
  have h6 : x ^ 2 + (b - 1) * x + c > 0 := h4 x
  have h7 : f x ^ 2 + (b - 1) * f x + c > 0 := by
    have h8 : ∀ x : ℝ, x ^ 2 + (b - 1) * x + c > 0 := h4
    specialize h8 (f x)
    simpa using h8
  linarith