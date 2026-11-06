import Mathlib

theorem algebra_308947 {A B : ℝ × ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (h1 : B = (-A.2, A.1)) (h2 : 2 * A + B = (7, 9)) :
    B = (-11 / 5, 23 / 5) := by
  rw [h1] at h2
  have eq1 : 2 * A.1 - A.2 = 7 := by
    simp [Prod.ext_iff] at h2 ⊢ 
    linarith
  have eq2 : 2 * A.2 + A.1 = 9 := by
    simp [Prod.ext_iff] at h2 ⊢
    linarith
  have ha1 : A.1 = 23 / 5 := by
    linarith [eq1, eq2]
  have ha2 : A.2 = 11 / 5 := by
    linarith [eq1, ha1]
  have hb1 : B.1 = -11 / 5 := by
    rw [h1]
    simp [ha2]
    all_goals linarith
  have hb2 : B.2 = 23 / 5 := by
    rw [h1]
    simp [ha1]
    all_goals linarith
  exact Prod.ext hb1 hb2