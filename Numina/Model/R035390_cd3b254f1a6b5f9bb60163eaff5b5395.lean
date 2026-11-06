import Mathlib

theorem algebra_2693 {a b c d : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 * (a * x ^ 5 + b * x ^ 3 + c * x) / (x ^ 4 + d * x ^ 2)) (h : f 1 = 1) : f (-1) = -1 := by
  have eq1 : f 1 = 1 ^ 2 * (a * 1 ^ 5 + b * 1 ^ 3 + c * 1) / (1 ^ 4 + d * 1 ^ 2) := hf 1
  rw [eq1] at h
  -- h is now 1 ^ 2 * (a * 1 ^ 5 + b * 1 ^ 3 + c * 1) / (1 ^ 4 + d * 1 ^ 2) = 1
  -- Simplify h
  have eq2 : (a + b + c) / (1 + d) = 1 := by
    norm_num at h ⊢
    <;> nlinarith
  -- Derive a + b + c = 1 + d from eq2, need to prove 1 + d ≠ 0.
  have h1 : 1 + d ≠ 0 := by
    by_contra h1
    have eq4 : (a + b + c) / (1 + d) = 0 := by
      rw [h1]
      norm_num
    nlinarith [eq4, eq2]
  -- Now we can derive a + b + c = 1 + d
  have eq3 : a + b + c = 1 + d := by
    have eq5 : (a + b + c) / (1 + d) = 1 := eq2
    have h1' : 1 + d ≠ 0 := h1
    have eq7 : a + b + c = 1 + d := by
      field_simp [h1'] at eq5 ⊢
      <;> nlinarith
    linarith
  -- Now compute f (-1).
  have eq4 : f (-1) = (-1) ^ 2 * (a * (-1) ^ 5 + b * (-1) ^ 3 + c * (-1)) / ((-1) ^ 4 + d * (-1) ^ 2) := hf (-1)
  rw [eq4]
  have eq6 : (-1 : ℝ) ^ 2 * (a * (-1 : ℝ) ^ 5 + b * (-1 : ℝ) ^ 3 + c * (-1 : ℝ)) = - (a + b + c) := by
    nlinarith
  have eq7 : (-1 : ℝ) ^ 4 + (d * (-1 : ℝ) ^ 2) = (1 + d) := by
    nlinarith
  rw [eq6, eq7]
  have eq3' : a + b + c = 1 + d := eq3
  rw [eq3']
  -- Now we have $-(1 + d) / (1 + d) = -1$.
  field_simp [h1]