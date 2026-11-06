import Mathlib

theorem algebra_135634 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : Real.sqrt x - Real.sqrt y = 1) (h2 : Real.sqrt (8 * x + 7) - Real.sqrt (8 * y + 7) = 2) :
    x = 9 / 4 ∧ y = 1 / 4 := by
  have h1' : Real.sqrt x = Real.sqrt y + 1 := by linarith
  have eq1 : x = y + 2 * Real.sqrt y + 1 := by
    calc
      x = (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt hx]
      _ = (Real.sqrt y + 1) ^ 2 := by rw [h1']
      _ = y + 2 * Real.sqrt y + 1 := by
        have h3 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
        nlinarith [h3]
  have h2' : Real.sqrt (8 * x + 7) = Real.sqrt (8 * y + 7) + 2 := by linarith
  have eq2 : (8 * x + 7) = (8 * y + 7) + 4 * Real.sqrt (8 * y + 7) + 4 := by
    calc
      (8 * x + 7) = (Real.sqrt (8 * x + 7)) ^ 2 := by rw [Real.sq_sqrt]; linarith
      _ = (Real.sqrt (8 * y + 7) + 2) ^ 2 := by rw [h2']
      _ = (Real.sqrt (8 * y + 7)) ^ 2 + 4 * Real.sqrt (8 * y + 7) + 4 := by ring
      _ = (8 * y + 7) + 4 * Real.sqrt (8 * y + 7) + 4 := by
        have h3 : (Real.sqrt (8 * y + 7)) ^ 2 = 8 * y + 7 := by
          apply Real.sq_sqrt
          linarith
        nlinarith [h3]

  have eq3 : 2 * x - 2 * y - 1 = Real.sqrt (8 * y + 7) := by
    nlinarith [eq2]

  have eq4 : 4 * Real.sqrt y + 1 = Real.sqrt (8 * y + 7) := by
    nlinarith [eq3, eq1]

  have eq5 : (4 * Real.sqrt y + 1)^2 = (8 * y + 7) := by
    calc
      (4 * Real.sqrt y + 1)^2 = (Real.sqrt (8 * y + 7)) ^ 2 := by rw [eq4]
      _ = 8 * y + 7 := Real.sq_sqrt (by linarith)

  have eq6 : 16 * (Real.sqrt y) ^ 2 + 8 * Real.sqrt y + 1 = 8 * y + 7 := by
    nlinarith [eq5]

  have h3 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  have eq7 : 16 * y + 8 * Real.sqrt y + 1 = 8 * y + 7 := by
    nlinarith [eq6, h3]

  have eq8 : 8 * y + 8 * Real.sqrt y - 6 = 0 := by
    nlinarith [eq7]

  have h4 : Real.sqrt y ≥ 0 := Real.sqrt_nonneg y

  have h5 : Real.sqrt y = 1 / 2 := by
    nlinarith [sq_nonneg (Real.sqrt y + 3 / 2), sq_nonneg (Real.sqrt y - 1 / 2), h4, h3]

  have eq9 : y = 1 / 4 := by
    calc
      y = (Real.sqrt y) ^ 2 := by
        rw [Real.sq_sqrt hy]
      _ = (1 / 2) ^ 2 := by
        rw [h5]
      _ = (1 : ℝ) / 4 := by
        norm_num

  have eq10 : Real.sqrt x = 3 / 2 := by
    have : Real.sqrt x = Real.sqrt y + 1 := by linarith
    rw [h5] at this
    linarith

  have eq11 : x = 9 / 4 := by
    calc
      x = (Real.sqrt x) ^ 2 := by
        rw [Real.sq_sqrt hx]
      _ = (3 / 2) ^ 2 := by
        rw [eq10]
      _ = 9 / 4 := by
        norm_num

  constructor
  · linarith [eq11]
  · linarith [eq9]