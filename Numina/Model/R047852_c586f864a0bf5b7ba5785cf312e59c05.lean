import Mathlib

theorem algebra_81248 {P : Polynomial ℝ} (hP : ∀ t, P.eval t = P.eval 1 * t ^ 2 + P.eval (P.eval 1) * t + P.eval (P.eval (P.eval 1))) :
    P.eval (P.eval (P.eval (P.eval 1))) ≤ 1 / 9 := by 
  have eq1 := hP 1
  have eq2 := hP (P.eval 1)
  have eq3 := hP (P.eval (P.eval 1))
  have eq4 := hP (P.eval (P.eval (P.eval 1)))
  have eq1' := hP 0
  have eq2' := hP 2
  have h1 : P.eval (P.eval (P.eval 1)) = - P.eval (P.eval 1) := by 
    nlinarith 
  have eq6 : (P.eval 1 + 1) * (P.eval (P.eval 1)) ^ 2 = 0 := by 
    have eq3' := hP (P.eval (P.eval 1))
    simp [h1] at eq3' 
    nlinarith 
  have eq7 : P.eval 1 + 1 = 0 ∨ (P.eval (P.eval 1) ) ^ 2 = 0 := by 
    cases (mul_eq_zero.1 eq6) with
    | inl h => 
      left 
      linarith 
    | inr h => 
      right 
      simpa using h 
  cases eq7 with 
  | inl h => 
    have ha1 : P.eval 1 = -1 := by linarith 
    have hb1 : P.eval (P.eval 1) = -1 / 3 := by 
      have eq2' := hP (P.eval 1)
      rw [ha1] at eq2 
      norm_num [ha1] at eq2 
      nlinarith [hP (-1), ha1]
    have hc1 : P.eval (P.eval (P.eval 1)) = 1 / 3 := by
      rw [hb1] at h1 
      nlinarith 
    have h3 : P.eval (P.eval (P.eval (P.eval 1))) = 1 / 9 := by 
      rw [hc1]
      nlinarith [hP (1 / 3), ha1, hb1, hc1]
    linarith 
  | inr h => 
    have hb0 : P.eval (P.eval 1) = 0 := by
      simp at h 
      linarith 
    have hc0 : P.eval (P.eval (P.eval 1)) = 0 := by 
      rw [hb0] at h1 
      nlinarith 
    have h4 : P.eval (P.eval (P.eval (P.eval 1))) = 0 := by 
      rw [hc0]
      nlinarith [hP 0, hb0, hc0]
    linarith