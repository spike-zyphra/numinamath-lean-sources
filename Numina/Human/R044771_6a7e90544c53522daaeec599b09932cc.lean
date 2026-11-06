import Mathlib

theorem algebra_5131 {F : ℝ → ℝ} (ha : a ≠ 0) (hF : ∃ a b c, F = fun x => a * x ^ 2 + b * x + c)
    (hF1 : F 1 = 11) (hF2 : F 2 = 13) (hF3 : F 3 = 17) : F 4 = 23 := by 
  obtain ⟨a, b, c, hF_eq⟩ := hF
  have eq1 : a * 1 ^ 2 + b * 1 + c = 11 := by 
    rw [hF_eq] at hF1
    exact hF1
  have eq2 : a * 2 ^ 2 + b * 2 + c = 13 := by 
    rw [hF_eq] at hF2
    exact hF2
  have eq3 : a * 3 ^ 2 + b * 3 + c = 17 := by 
    rw [hF_eq] at hF3
    exact hF3
  have eq4 : a * 4 ^ 2 + b * 4 + c = 23 := by 
    linarith
  rw [hF_eq]
  exact eq4