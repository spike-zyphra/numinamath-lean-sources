import Mathlib

theorem algebra_146606 (a b : ℝ) (A B C : ℝ × ℝ)
    (hA : A = (2 * a - b, a + b + 1)) (hB : B = (3 * a + 2 * b, 3 * a + 2 * b - 2))
    (hC : C = (5, -2)) (hmid : C = ((A.1 + B.1) / 2, (A.2 + B.2) / 2)) :
    Real.sqrt ((B.1 - A.1)^2 + (B.2 - A.2)^2) = 2 * Real.sqrt 37 := by
  rw [hC, hA, hB] at hmid
  simp [Prod.ext_iff] at hmid
  have eq1 : 10 = 5 * a + b := by
    linarith 
  have eq2 : -3 = 4 * a + 3 * b := by
    linarith 
  have ha : a = 3 := by
    nlinarith 
  have hb : b = -5 := by 
    linarith [eq1, ha]
  have hA11 : A = (11, -1) := by
    rw [hA]
    simp [ha, hb]
    all_goals norm_num
  have hB11 : B = (-1, -3) := by 
    rw [hB]
    simp [ha, hb]
    all_goals norm_num
  rw [hA11, hB11]
  have h1 : Real.sqrt ((-1 - 11 : ℝ) ^ 2 + (-3 - -1 : ℝ) ^ 2) = Real.sqrt 148 := by
    norm_num 
  have h2 : Real.sqrt ((-1 - 11 : ℝ) ^ 2 + (-3 - -1 : ℝ) ^ 2) = 2 * Real.sqrt 37 := by
    rw [h1]
    have h3 : Real.sqrt (148 : ℝ) = 2 * Real.sqrt 37 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h3]
  exact h2