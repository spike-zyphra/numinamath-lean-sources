import Mathlib

theorem algebra_4091 {A B C : ℝ × ℝ}
    (hA : A = (2, -2)) (hB : B = (14, 4)) (hC : C - B = 1 / 3 * (B - A)) :
    C = (18, 6) := by
  rw [hA, hB] at hC
  have hC1 : C.1 - 14 = 4 := by
    simp [Prod.ext_iff] at hC ⊢
    linarith
  have hC2 : C.2 - 4 = 2 := by
    simp [Prod.ext_iff] at hC ⊢
    linarith
  have h1 : C.1 = 18 := by
    linarith
  have h2 : C.2 = 6 := by
    linarith
  simp [Prod.ext_iff, h1, h2]