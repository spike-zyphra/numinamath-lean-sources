import Mathlib

theorem algebra_201875 {a : ℕ → ℝ} (P : ℝ → ℝ)
    (hP : P = fun x => x^5 + a 4 * x^4 + a 3 * x^3 + a 2 * x^2 + a 1 * x + a 0)
    (hP1 : P 2014 = 1) (hP2 : P 2015 = 2) (hP3 : P 2016 = 3)
    (hP4 : P 2017 = 4) (hP5 : P 2018 = 5) :
    P 2013 = -120 := by
  simp [hP] at hP1 hP2 hP3 hP4 hP5 ⊢
  linarith