import Mathlib

theorem algebra_310212 {x : ℝ} (hx : x = (1 + Real.sqrt 1994) / 2) :
    (4 * x^3 - 1997 * x - 1994)^2001 = -1 := by
  have h1 : 2 * x - 1 = Real.sqrt 1994 := by
    rw [hx]
    ring_nf
    <;> linarith [Real.sqrt_nonneg 1994]

  have h2 : (2 * x - 1) ^ 2 = 1994 := by
    calc
      (2 * x - 1) ^ 2 = (Real.sqrt 1994) ^ 2 := by rw [h1]
      _ = 1994 := Real.sq_sqrt (by norm_num)
  have h3 : 4 * x^2 - 4 * x - 1993 = 0 := by
    nlinarith [h2]

  have h4 : 4 * x^3 = 1997 * x + 1993 := by
    have eq1 : 4 * x^2 = 4 * x + 1993 := by
      linarith [h3]
    calc
      4 * x^3 = x * (4 * x^2) := by ring
      _ = x * (4 * x + 1993) := by rw [eq1]
      _ = 4 * x^2 + 1993 * x := by ring
      _ = (4 * x + 1993) + 1993 * x := by rw [eq1]
      _ = 1997 * x + 1993 := by ring

  have h5 : 4 * x^3 - 1997 * x - 1994 = -1 := by
    linarith [h4]

  rw [h5]
  norm_num