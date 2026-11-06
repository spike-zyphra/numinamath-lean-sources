import Mathlib

theorem algebra_306430 (E1 E2 : ℝ × ℝ)
    (hE1 : E1 = (2, 1)) (hE2 : E2 = (2, -1))
    (e1 e2 : ℝ × ℝ)
    (he1 : e1 = E1) (he2 : e2 = E2)
    (P : ℝ × ℝ)
    (hP : P.1 ^ 2 / 4 - P.2 ^ 2 = 1)
    (a b : ℝ)
    (ha : P.1 = a * e1.1 + b * e2.1) (hb : P.2 = a * e1.2 + b * e2.2) :
    a ^ 2 + b ^ 2 ≥ 1 / 2 := by
  rw [hE1] at he1
  rw [hE2] at he2
  have ha1 : P.1 = a * 2 + b * 2 := by
    rw [ha]
    simp [he1, he2]
    <;> ring
  have hb1 : P.2 = a - b := by
    rw [hb]
    simp [he1, he2]
    <;> ring
  rw [ha1] at hP
  rw [hb1] at hP
  have h_eq : (a + b) ^ 2 - (a - b) ^ 2 = 1 := by
    nlinarith
  have h_eq3 : a * b = 1 / 4 := by
    nlinarith [h_eq]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b - 1 / 4)]