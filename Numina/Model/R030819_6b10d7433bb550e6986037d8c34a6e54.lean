import Mathlib

theorem algebra_165396 {f : ℝ → ℝ} (h : ∀ x y, (x - y) * f (x + y) - (x + y) * f (x - y) = 4 * x * y * (x ^ 2 - y ^ 2)) :
    ∃ c, ∀ x, f x = x ^ 3 + c * x := by 
  -- Step 1: Establish f 0 = 0
  have h1 := h 0 0
  norm_num at h1
  have h2 := h 1 (-1)
  norm_num at h2 
  have h3 : f 0 = 0 := by linarith 
  -- Now we use the Existential quantifier with f 1 -1 as the constant
  use (f 1 - 1)
  intro x 
  have eq4 := h ((x + 1) / 2) ((x - 1) / 2)
  -- Simplify eq4
  ring_nf at eq4 
  -- Prove that f x = x^3 + c*x with c = f 1 -1
  have eq5 : f x - x * f 1 = x ^ 3 - x := by
    nlinarith 
  -- Rearrange to target form
  have eq7 : f x = x ^ 3 + (f 1 - 1) * x := by
    linarith [eq5]
  simp [eq7]
  all_goals ring_nf <;> nlinarith
  all_goals linarith