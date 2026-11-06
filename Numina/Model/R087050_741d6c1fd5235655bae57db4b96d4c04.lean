import Mathlib

theorem algebra_126682 {a b c d : ℝ} (P : ℝ → ℝ)
    (hP : P = fun x => x^4 + a * x^3 + b * x^2 + c * x + d)
    (hP1 : P 1 = 2004) (hP2 : P 2 = 4008) (hP3 : P 3 = 6012) :
    (P 11 + P (-7)) / 4 = 5244 := by

  have h1_eq : 1^4 + a * 1^3 + b * 1^2 + c * 1 + d = 2004 := by
    rw [hP] at hP1
    simpa using hP1

  have h2_eq : 2^4 + a * 2^3 + b * 2^2 + c * 2 + d = 4008 := by
    rw [hP] at hP2
    simpa using hP2

  have h3_eq : 3^4 + a * 3^3 + b * 3^2 + c * 3 + d = 6012 := by
    rw [hP] at hP3
    simpa using hP3

  have h11_eq : P 11 = 11^4 + a * 11^3 + b * 11^2 + c * 11 + d := by
    rw [hP]

  have h7_eq : P (-7) = (-7)^4 + a * (-7)^3 + b * (-7)^2 + c * (-7) + d := by
    rw [hP]

  rw [h11_eq, h7_eq]
  linarith [h1_eq, h2_eq, h3_eq]