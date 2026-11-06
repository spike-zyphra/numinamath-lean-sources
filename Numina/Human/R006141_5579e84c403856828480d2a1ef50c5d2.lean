import Mathlib

open Real
/- if  x = 1 / (1 - 1 / (2 + 1 / (1 - 1 / (2 + x))))), x >0, find the value of x-/
theorem algebra_13478 {x : ℝ} (hx : x > 0)
    (h : x = 1 / (1 - 1 / (2 + 1 / (1 - 1 / (2 + x))))) :
    x = sqrt 2 := by
    -- we need to show the Denominators are not zero --
  have h1 : x ≠ 0 := by linarith
  have h2 : 2 + x ≠ 0 := by nlinarith
  have h3 : 1 - 1 / (2 + x) ≠ 0 := by
    intro h4
    have h5 : 1 - 1 / (2 + x) = 0 := by linarith
    have h6 : 1 / (2 + x) = 1 := by linarith
    have h7 : 2 + x = 1 := by
      field_simp [h2] at h6
      linarith
    linarith
  have h4 : 1 + x ≠ 0 := by nlinarith
  -- then we simplify step by step 
  have eq1 : 1 - 1 / (2 + x) = (1 + x) / (2 + x) := by
    field_simp [h2]
    linarith
  have eq2 : 1 / (1 - 1 / (2 + x)) = (2 + x) / (1 + x) := by
    rw [eq1]
    field_simp [h4]
  have eq3 : 2 + (1 / (1 - 1 / (2 + x))) = (4 + 3 * x) / (1 + x) := by
    rw [eq2]
    field_simp [h4]
    ring
  have eq4 : 1 / (2 + (1 / (1 - 1 / (2 + x)))) = (1 + x) / (4 + 3 * x) := by
    rw [eq3]
    field_simp [(show 4 + 3 * x ≠ 0 by nlinarith [sq_nonneg x])]
  have eq5 : 1 - 1 / (2 + (1 / (1 - 1 / (2 + x)))) = (3 + 2 * x) / (4 + 3 * x) := by
    rw [eq4]
    field_simp [(show 4 + 3 * x ≠ 0 by nlinarith [sq_nonneg x])]
    ring
  have eq6 : x = (4 + 3 * x) / (3 + 2 * x) := by
    rw [eq5] at h
    field_simp [(show 3 + 2 * x ≠ 0 by nlinarith [sq_nonneg x])] at h ⊢
    nlinarith
  have h7 : x ^ 2 = 2 := by
    have h8 : 3 + 2 * x ≠ 0 := by nlinarith [sq_nonneg x]
    have eq7 : x * (3 + 2 * x) = 4 + 3 * x := by
      field_simp [h8] at eq6 ⊢
      linarith
    nlinarith [sq_nonneg x]
  have h8 : x = Real.sqrt 2 := by
    have h9 : x ≥ 0 := by linarith
    have h10 : x ^ 2 = 2 := h7
    have h11 : x = Real.sqrt 2 := by
      rw [←h10]
      field_simp [h9]
    exact h11
  exact h8
