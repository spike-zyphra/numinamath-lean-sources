import Mathlib


theorem algebra_112920 (f : ℝ → ℝ) :
    (∀ x y, (x - y) * f (x + y) - (x + y) * f (x - y) = 4 * x * y * (x ^ 2 - y ^ 2)) ↔
    ∃ c, ∀ x, f x = x ^ 3 + c * x := by
  constructor
  · -- Assume the functional equation holds, prove that f(x) = x^3 + c*x
    intro h
    have h1 : ∀ t s : ℝ, s * f t - t * f s = t * s * (t ^ 2 - s ^ 2) := by
      intro t s 
      have eq := h ((t + s) / 2) ((t - s) / 2)
      ring_nf at eq ⊢
      linarith
    have eq3 : ∃ c, ∀ x, f x = x ^ 3 + c * x := by
      use (f 1 - 1 : ℝ)
      intro x 
      by_cases ht : x = 0 
      · -- When  x = 0
        rw [ht]
        have h3 : f 0 = 0 := by
          have eq11 := h1 1 0 
          norm_num at eq11 ⊢ 
          linarith
        norm_num at h3 ⊢
        linarith
      · -- When x ≠ 0
        have eq4 : f x = x ^ 3 + (f 1 - 1) * x := by
          have eq11 := h1 x 1 
          have eq5 : (1 : ℝ) * f x - x * f 1 = x * (1 : ℝ) * (x ^ 2 - (1 : ℝ) ^ 2) := by 
            simpa using eq11
          have eq5' : (1 : ℝ) * f x - x * f 1 = x * (x ^ 2 - 1 : ℝ) := by
            linarith
          have eq6 : f x = x ^ 3 + (f 1 - 1) * x := by
            have eq7 : (1 : ℝ) * f x - x * f 1 = x * (x ^ 2 - 1 : ℝ) := eq5'
            have eq8 : f x = x * f 1 + x * (x ^ 2 - 1 : ℝ) := by
              linarith 
            have eq9 : f x = x ^ 3 + (f 1 - 1) * x := by
              nlinarith 
            linarith 
          linarith
        linarith
    exact eq3
  · -- Assume the existence of c, prove the functional equation.
    rintro ⟨c, hc⟩ 
    intro x y
    have h15 : f (x + y) = (x + y) ^ 3 + c * (x + y) := hc (x + y)
    have h16 : f (x - y) = (x - y) ^ 3 + c * (x - y) := hc (x - y)
    rw [h15, h16]
    ring