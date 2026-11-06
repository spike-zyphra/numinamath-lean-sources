import Mathlib

theorem algebra_47175 {P : ℝ → ℝ} (hP : ∃ a b c d : ℝ, P = fun x => a*x^3 + b*x^2 + c*x + d)
    (hP1 : P 11 = 11) (hP2 : P 12 = 12) (hP3 : P 13 = 14) (hP4 : P 14 = 15) :
    P 15 = 13 := by
  rcases hP with ⟨a, b, c, d, hP_def⟩
  have eq1 : a * 11 ^ 3 + b * 11 ^ 2 + c * 11 + d = 11 := by
    rw [hP_def] at hP1
    simpa using hP1
  have eq2 : a * 12 ^ 3 + b * 12 ^ 2 + c * 12 + d = 12 := by
    rw [hP_def] at hP2
    simpa using hP2
  have eq3 : a * 13 ^ 3 + b * 13 ^ 2 + c * 13 + d = 14 := by
    rw [hP_def] at hP3
    simpa using hP3
  have eq4 : a * 14 ^ 3 + b * 14 ^ 2 + c * 14 + d = 15 := by
    rw [hP_def] at hP4
    simpa using hP4
  have eq5 : P 15 = a * 15 ^ 3 + b * 15 ^ 2 + c * 15 + d := by
    rw [hP_def]
    all_goals norm_num
    <;> ring
  rw [eq5]
  linarith [eq1, eq2, eq3, eq4]