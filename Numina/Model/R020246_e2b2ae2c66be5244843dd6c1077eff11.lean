import Mathlib


theorem algebra_276617 {a b c A B C x : ℝ} (ha : a ≠ 0) (hroots : ∃ x, a * x ^ 2 + b * x + c = 0 ∧ A * x ^ 2 + B * x + C = 0)
    (hne : {x | a * x ^ 2 + b * x + c = 0} ≠ {x | A * x ^ 2 + B * x + C = 0}) :
    (A * c - C * a) ^ 2 = (A * b - B * a) * (B * c - C * b) := by

  rcases hroots with ⟨x, h2, h3⟩

  have h4 : a * x ^ 2 + b * x + c = 0 := h2
  have h5 : A * x ^ 2 + B * x + C = 0 := h3
  
  have hc : c = -a * x ^ 2 - b * x := by
    linarith

  have hC : C = -A * x ^ 2 - B * x := by
    linarith

  have eq1 : A * c - C * a = x * (a * B - A * b) := by
    rw [hc, hC]
    nlinarith [sq_nonneg (x)]

  have eq2 : B * c - C * b = x ^ 2 * (A * b - B * a) := by
    rw [hc, hC]
    nlinarith [sq_nonneg (x)]

  calc
    (A * c - C * a) ^ 2 = (x * (a * B - A * b)) ^ 2 := by rw [eq1]
    _ = x ^ 2 * (a * B - A * b) ^ 2 := by ring
    _ = x ^ 2 * (A * b - B * a) ^ 2 := by 
      have eq3 : (a * B - A * b) ^ 2 = (A * b - B * a) ^ 2 := by 
        nlinarith 
      rw [eq3]
    _ = (A * b - B * a) * (x ^ 2 * (A * b - B * a)) := by 
      ring_nf 
    _ = (A * b - B * a) * (B * c - C * b) := by
      rw [eq2]