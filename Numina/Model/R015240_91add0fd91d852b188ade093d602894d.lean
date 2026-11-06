import Mathlib

theorem algebra_35455 {x y z : ℝ} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y)
    (h : (y * z - x ^ 2) / (1 - x) = (z * x - y ^ 2) / (1 - y)) :
    (y * z - x ^ 2) / (1 - x) = x + y + z ∧ (z * x - y ^ 2) / (1 - y) = x + y + z := by
  have h1 : x - 1 ≠ 0 := by
    intro h2
    apply hx
    linarith
  have h2' : 1 - x ≠ 0 := by
    intro h2
    apply hx
    linarith
  have h3' : 1 - y ≠ 0 := by
    intro h3
    apply hy
    linarith
  have eq1 : (y * z - x ^ 2) * (1 - y) = (z * x - y ^ 2) * (1 - x) := by
    have eq2 : (y * z - x ^ 2) / (1 - x) = (z * x - y ^ 2) / (1 - y) := h 
    field_simp [(show 1 - x ≠ 0 by assumption), (show 1 - y ≠ 0 by assumption)] at eq2 ⊢ 
    linarith 
  constructor
  · -- Prove that the first expression equals x + y + z
    have eq3 : (y * z - x ^ 2) / (1 - x) = x + y + z := by
      have eq4 : (y * z - x ^ 2) = (x + y + z) * (1 - x) := by 
        have eq5 : (y * z - x ^ 2) * (1 - y) = (z * x - y ^ 2) * (1 - x) := eq1 
        nlinarith [sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
          intro h'
          apply hxy 
          linarith 
        ), sq_pos_of_ne_zero (show (1 - x : ℝ) ≠ 0 by
          intro h'
          apply hx 
          linarith 
        ), sq_pos_of_ne_zero (show (1 - y : ℝ) ≠ 0 by
          intro h'
          apply hy 
          linarith 
        ), sq_nonneg (x - y), sq_nonneg (x + y - z), sq_nonneg (x - 1), sq_nonneg (y - 1)]
      field_simp [(show 1 - x ≠ 0 by assumption)]
      linarith [eq4]
    exact eq3
  · -- Prove the second expression equals x + y + z.
    have eq5 : (z * x - y ^ 2) / (1 - y) = x + y + z := by
      have eq6 : (z * x - y ^ 2) = (x + y + z) * (1 - y) := by 
        have eq7 : (y * z - x ^ 2) * (1 - y) = (z * x - y ^ 2) * (1 - x) := eq1 
        nlinarith [sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
          intro h'
          apply hxy 
          linarith 
        ), sq_pos_of_ne_zero (show (1 - x : ℝ) ≠ 0 by
          intro h'
          apply hx 
          linarith 
        ), sq_pos_of_ne_zero (show (1 - y : ℝ) ≠ 0 by
          intro h'
          apply hy 
          linarith 
        ), sq_nonneg (x - y), sq_nonneg (x + y - z), sq_nonneg (x - 1), sq_nonneg (y - 1)]
      field_simp [(show 1 - y ≠ 0 by assumption)]
      linarith [eq6]
    exact eq5