import Mathlib

theorem algebra_120117 (P Q : ℝ × ℝ) (hP : P = (3, 2)) (hQ : Q ∈ {(x, y) | x - 2 * y + 11 = 0})
    (hinc : (Q.2 - P.2) / (Q.1 - P.1) = 3 / 4) :
    Real.sqrt ((Q.1 - P.1)^2 + (Q.2 - P.2)^2) = 25 := by
  have h1 : Q.1 - 2 * Q.2 + 11 = 0 := by
    simpa using hQ
  have hP1 : P.1 = 3 := by 
    simp [hP]
  have hP2 : P.2 = 2 := by 
    simp [hP]

  have h2 : Q.1 - P.1 ≠ 0 := by 
    by_contra h
    have h3 : Q.1 = P.1 := by 
      linarith
    have h4 : Q.1 = 3 := by
      rw [hP1] at h3
      linarith
    have h5 : Q.2 = 7 := by 
      rw [h4] at h1
      linarith
    -- Now we use h4 and h5 to evaluate hinc
    rw [show P.1 = (3 : ℝ) by simp [hP], show P.2 = (2 : ℝ) by simp [hP], h4, h5] at hinc
    norm_num at hinc 
    all_goals linarith 
  -- Derive slope condition without division 
  have h3 : Q.2 - 2 = 3 / 4 * (Q.1 - 3) := by
    rw [hP1, hP2] at hinc
    have h4' : Q.1 - 3 ≠ 0 := by
      intro h
      apply h2
      linarith 
    field_simp [h4'] at hinc 
    linarith 
  have h4 : 4 * (Q.2 - 2) = 3 * (Q.1 - 3) := by 
    linarith [h3]
  -- Solve the system of equations
  have eq1 : Q.1 = 23 := by
    linarith [h1, h4]
  have eq2 : Q.2 = 17 := by
    linarith [h1, h4]

  have h5 : (Q.1 - P.1)^2 + (Q.2 - P.2)^2 = (25 : ℝ) ^2 := by
    rw [hP1, hP2, eq1, eq2]
    norm_num 
  rw [h5]
  exact Real.sqrt_sq (by norm_num)