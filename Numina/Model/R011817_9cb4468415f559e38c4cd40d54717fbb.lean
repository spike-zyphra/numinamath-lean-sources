import Mathlib


theorem algebra_314811 (x y : ℤ) (h : 15 * x^2 * y^2 = 35 * x^2 - 3 * y^2 + 412) :
    15 * x^2 * y^2 = 960 := by

  have h1 : 15 * x^2 * y^2 + 3 * y^2 = 35 * x^2 + 412 := by
    linarith

  have h3 : (5 * x^2 + 1) * (9 * y^2 - 21) = 1215 := by
    nlinarith

  have h4 : (5 * x^2 + 1) ∣ 1215 := by
    use (9 * y^2 - 21)
    all_goals
      linarith [h3]

  have h5 : (5 * x^2 + 1) ≥ 1 := by
    nlinarith [sq_nonneg x]

  have h6 : (5 * x^2 + 1) ≤ 1215 := by
    exact Int.le_of_dvd (by norm_num) h4

  have h7 : (5 * x^2 + 1) = 1 ∨ (5 * x^2 + 1) = 3 ∨ (5 * x^2 + 1) = 9 ∨ (5 * x^2 + 1) = 27 ∨ (5 * x^2 + 1) = 81 ∨ (5 * x^2 + 1) = 243 ∨ (5 * x^2 + 1) = 5 ∨ (5 * x^2 + 1) = 15 ∨ (5 * x^2 + 1) = 45 ∨ (5 * x^2 + 1) = 135 ∨ (5 * x^2 + 1) = 405 ∨ (5 * x^2 + 1) = 1215 := by
    interval_cases h8 : (5 * x^2 + 1) <;> omega

  rcases h7 with (h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8 | h8)
  · -- When (5 * x^2 + 1) = 1
    have h15 : 5 * x^2 + 1 = 1 := by linarith
    have h17 : 9 * y^2 - 21 = 1215 := by
      nlinarith [h3, h15]
    omega
  · -- When (5 * x^2 + 1) = 3
    have h15 : 5 * x^2 + 1 = 3 := by linarith
    omega
  · -- When (5 * x^2 + 1) = 9
    have h15 : 5 * x^2 + 1 = 9 := by linarith
    omega
  · -- When (5 * x^2 + 1) = 27
    have h15 : 5 * x^2 + 1 = 27 := by linarith
    omega
  · -- When (5 * x^2 + 1) = 81
    have h15 : 5 * x^2 + 1 = 81 := by linarith
    have h18 : 9 * y^2 - 21 = 15 := by
      nlinarith [h3, h15]
    have h19 : y^2 = 4 := by
      nlinarith
    have h20 : x^2 = 16 := by
      nlinarith
    nlinarith [h19, h20]
  · -- When (5 * x^2 + 1) = 243
    have h15 : 5 * x^2 + 1 = 243 := by linarith
    omega
  · -- When (5 * x^2 + 1) = 5
    have h15 : 5 * x^2 + 1 = 5 := by linarith
    omega
  · -- When (5 * x^2 + 1) = 15
    have h15 : 5 * x^2 + 1 = 15 := by linarith
    omega
  · -- When (5 * x^2 + 1) = 45
    have h15 : 5 * x^2 + 1 = 45 := by linarith
    omega
  · -- When (5 * x^2 + 1) = 135
    have h15 : 5 * x^2 + 1 = 135 := by linarith
    omega
  · -- When (5 * x^2 + 1) = 405
    have h15 : 5 * x^2 + 1 = 405 := by linarith
    omega
  · -- When (5 * x^2 + 1) = 1215
    have h15 : 5 * x^2 + 1 = 1215 := by linarith
    omega