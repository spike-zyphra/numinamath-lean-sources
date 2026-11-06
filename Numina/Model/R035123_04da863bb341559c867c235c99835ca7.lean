import Mathlib

theorem calculus_22944 {A B P : ℝ × ℝ}
    (hA : A = (0, 0)) (hB : B = (5, 1)) (hP : P - A = 4 * (B - P)) :
    ∃ t u, P = t * A + u * B := by
  use 1 / 5, 4 / 5
  have eq1 : P.1 - A.1 = 4 * (B.1 - P.1) := by
    have h1 := congrArg Prod.fst hP
    simp [hA, hB] at h1 ⊢
    linarith
  have eq2 : P.2 - A.2 = 4 * (B.2 - P.2) := by
    have h2 := congrArg Prod.snd hP
    simp [hA, hB] at h2 ⊢
    linarith
  have eq3 : P.1 = 4 := by
    simp [hA, hB] at eq1 ⊢
    linarith
  have eq4 : P.2 = 4 / 5 := by
    simp [hA, hB] at eq2 ⊢
    linarith
  simp [Prod.ext_iff, hA, hB, eq3, eq4]
  all_goals norm_num