import Mathlib

theorem algebra_35535 {R I G T M S P N L : ℝ}
    (hR : R * I + G + S * P = 50) (hR' : R * I + T + M = 63)
    (hG : G + T + S * P = 25) (hSP : S * P + M = 13) (hM : M + R * I = 48)
    (hN : N = 1) :
    L * M * T + S * P * R * I * N * G = 2023 ↔ L = 341 / 40 := by

  have eq1 : M = 48 - R * I := by
    linarith

  have eq2 : S * P = R * I - 35 := by
    linarith [hSP, eq1]

  have eq3 : T = 15 := by
    rw [eq1] at hR'
    linarith

  have eq4 : G = 5 := by
    rw [eq3, eq2] at hG
    linarith

  have eq6 : R * I = 40 := by
    rw [eq4, eq2] at hR
    linarith

  have eq7 : M = 8 := by
    rw [eq6] at eq1
    linarith

  have eq8 : S * P = 5 := by
    rw [eq6] at eq2
    linarith

  constructor
  · -- Forward implication
    intro h
    rw [eq7, eq3, hN, eq4] at h
    nlinarith
  · -- Backward implication
    intro h
    rw [h, eq7, eq3, hN, eq4]
    nlinarith