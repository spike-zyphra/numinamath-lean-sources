import Mathlib

theorem algebra_242090 (a b c d : ℝ) (h : a^2 + d^2 - 2 * (a * b + b * c + c * d - b^2 - c^2) = 0) :
    a = b ∧ b = c ∧ c = d := by
  have h1 : (a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 = 0 := by 
    nlinarith 
  have h2 : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
  have h3 : (b - c) ^ 2 ≥ 0 := sq_nonneg (b - c)
  have h4 : (c - d) ^ 2 ≥ 0 := sq_nonneg (c - d)
  have h5 : (a - b) ^ 2 = 0 := by
    linarith 
  have h6 : (b - c) ^ 2 = 0 := by
    linarith 
  have h7 : (c - d) ^ 2 = 0 := by
    linarith 
  -- Now, from the squares being zero, the bases must be zero:
  have h8 : a - b = 0 := by
    nlinarith 
  have h9 : a = b := by
    linarith 
  -- Similarly, from h6:
  have h10 : b - c = 0 := by
    nlinarith 
  have h11 : b = c := by
    linarith 
  -- Similarly, from h7:
  have h12 : c - d = 0 := by
    nlinarith 
  have h13 : c = d := by
    linarith 
  exact ⟨h9, h11, h13⟩