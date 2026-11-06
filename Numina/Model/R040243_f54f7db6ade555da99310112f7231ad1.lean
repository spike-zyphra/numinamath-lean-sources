import Mathlib

theorem algebra_192575 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 + b * x + c)
    (h : ∀ x, f x ≠ x) : ∀ x, f (f x) ≠ x := by

  have h1 : ∀ x : ℝ, f x > x := by
    intro x
    have h2 : f x - x > 0 := by
      have eq1 : f x - x = x ^ 2 + (b - 1) * x + c := by
        rw [hf x]
        ring
      have h3 : x ^ 2 + (b - 1) * x + c > 0 := by
        have h5 : ∀ y : ℝ, y ^ 2 + (b - 1) * y + c ≠ 0 := by
          intro y
          have h6 : f y ≠ y := h y
          have eq2 : f y - y = y ^ 2 + (b - 1) * y + c := by
            rw [hf y]
            ring
          have h7 : f y - y ≠ 0 := by
            intro h8
            have h9 : f y = y := by
              linarith
            contradiction
          have h8 : y ^ 2 + (b - 1) * y + c ≠ 0 := by
            rw [← eq2]
            exact h7
          assumption
        nlinarith [sq_nonneg (x + (b - 1) / 2), sq_nonneg (x + (b - 1) / 2),
          show (c - ((b - 1) ^ 2) / 4) > 0 by
            by_contra h10
            push_neg at h10
            have h60 : ∃ y : ℝ, y ^ 2 + (b - 1) * y + c = 0 := by
              have h20 : ( (b - 1) ^ 2 / 4 ) ≥ c := by linarith
              use (- (b - 1) / 2 + Real.sqrt (( (b - 1) ^ 2 / 4 ) - c))
              nlinarith [ Real.sqrt_nonneg ((( (b - 1) ^ 2 / 4 ) - c)), Real.sq_sqrt (show (0 : ℝ) ≤ ((b - 1) ^ 2 / 4 - c) by nlinarith) ]
            rcases h60 with ⟨y, hy⟩
            have h51 : f y = y := by 
              rw [hf y]
              nlinarith [hy]
            have h52 : f y ≠ y := h y
            contradiction
        ]
      linarith [eq1, h3]
    linarith
  intro x
  have h4 : ∀ x : ℝ, f x > x := h1
  have h5 : f x > x := h4 x
  have h6 : f (f x) > f x := by
    have h7 : ∀ y : ℝ, f y > y := h4
    specialize h7 (f x)
    linarith
  have h7 : f (f x) > x := by
    linarith [h5, h6]
  intro h8
  have h9 : f (f x) = x := by
    linarith [h8]
  linarith [h7, h9]