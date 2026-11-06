import Mathlib

theorem algebra_5131 {F : ℝ → ℝ} (ha : a ≠ 0) (hF : ∃ a b c, F = fun x => a * x ^ 2 + b * x + c)
    (hF1 : F 1 = 11) (hF2 : F 2 = 13) (hF3 : F 3 = 17) : F 4 = 23 := by
  rcases hF with ⟨a, b, c, hFeq⟩
  have eq1 : a * 1 ^ 2 + b * 1 + c = 11 := by
    rw [hFeq] at hF1
    simpa using hF1
  have eq2 : a * 2 ^ 2 + b * 2 + c = 13 := by 
    rw [hFeq] at hF2
    simpa using hF2
  have eq3 : a * 3 ^ 2 + b * 3 + c = 17 := by
    rw [hFeq] at hF3
    simpa using hF3
  have eq4 : F 4 = a * 4 ^ 2 + b * 4 + c := by
    rw [hFeq]
  -- Solve the equations
  have ha1 : a = 1 := by 
    linarith
  have hb : b = -1 := by
    rw [ha1] at eq1 eq2
    linarith
  have hc : c = 11 := by 
    rw [ha1, hb] at eq1
    linarith
  rw [eq4]
  rw [ha1, hb, hc]
  norm_num