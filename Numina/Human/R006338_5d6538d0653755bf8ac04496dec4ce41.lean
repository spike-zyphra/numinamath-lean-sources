import Mathlib


/-
Theorem: For positive integer A and trip count N, if total cost M satisfies both:
M = A × N + 11 × (N-1) and M = 8 × A + 77, then N = 8.
-/
theorem my_favorite_theorem {A N M : ℤ}
  (hA : A > 0)                          -- A is positive cost component
  (h : M = A * N + 11 * (N - 1))        -- Cost formula for N trips
  (h' : M = 8 * A + 77)                 -- Given total cost
  : N = 8 := by

  -- Combine both cost equations
  have h₁ : A * N + 11 * (N - 1) = 8 * A + 77 := by
    rw [← h, h']

  -- Expand and transform to factorized form
  have h₂ : (A + 11) * N = 8 * (A + 11) := by
    calc
      (A + 11) * N = A * N + 11 * N := by ring
      _ = (A * N + 11 * (N - 1)) + 11 := by ring
      _ = (8 * A + 77) + 11           := by rw [h₁]
      _ = 8 * A + 88                 := by ring
      _ = 8 * (A + 11)               := by ring

  -- Non-zero denominator proof
  have hA : A + 11 ≠ 0 := by linarith [hA]

  -- Cancel (A + 11) from both sides
  apply_fun (· / (A + 11)) at h₂
  rw [mul_div_cancel_left₀ _ hA] at h₂
  have h₃ : 8 * (A + 11) / (A + 11) = 8 := by
    exact Int.mul_ediv_cancel 8 hA
  rw [h₃] at h₂
  exact h₂