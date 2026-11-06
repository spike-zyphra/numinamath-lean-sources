import Mathlib

theorem algebra_231429 {x y : ℝ} (h : 0 ≤ x ^ 3 + y) (h' : 0 ≤ y ^ 3 + x)
    (h'' : 0 ≤ x ^ 3 + x) (h''' : 0 ≤ y ^ 3 + y) :
    Real.sqrt (x ^ 3 + y) + Real.sqrt (y ^ 3 + x) =
    Real.sqrt (x ^ 3 + x) + Real.sqrt (y ^ 3 + y) → x = y := by

  intro heq

  have h1 : 0 ≤ x := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2), sq_nonneg (x + 1), sq_nonneg (y + 1)]

  have h2 : 0 ≤ y := by 
    nlinarith [sq_nonneg (y ^ 2), sq_nonneg (x ^ 2), sq_nonneg (y + 1), sq_nonneg (x + 1)]

  have eq1 : (Real.sqrt (x ^ 3 + y) + Real.sqrt (y ^ 3 + x)) ^ 2 = (Real.sqrt (x ^ 3 + x) + Real.sqrt (y ^ 3 + y)) ^ 2 := by
    rw [heq]

  have eq2 : (Real.sqrt (x ^ 3 + y) + Real.sqrt (y ^ 3 + x)) ^ 2 =
      (Real.sqrt (x ^ 3 + y)) ^ 2 + (Real.sqrt (y ^ 3 + x)) ^ 2 + 2 * (Real.sqrt (x ^ 3 + y) * Real.sqrt (y ^ 3 + x)) := by ring
  have eq3 : (Real.sqrt (x ^ 3 + x) + Real.sqrt (y ^ 3 + y)) ^ 2 =
      (Real.sqrt (x ^ 3 + x)) ^ 2 + (Real.sqrt (y ^ 3 + y)) ^ 2 + 2 * (Real.sqrt (x ^ 3 + x) * Real.sqrt (y ^ 3 + y)) := by ring

  rw [eq2, eq3] at eq1

  have eq4 : (Real.sqrt (x ^ 3 + y)) ^ 2 = x ^ 3 + y := Real.sq_sqrt (show 0 ≤ x ^ 3 + y by linarith)
  have eq5 : (Real.sqrt (y ^ 3 + x)) ^ 2 = y ^ 3 + x := Real.sq_sqrt (show 0 ≤ y ^ 3 + x by linarith)
  have eq6 : (Real.sqrt (x ^ 3 + x)) ^ 2 = x ^ 3 + x := Real.sq_sqrt (show 0 ≤ x ^ 3 + x by linarith)
  have eq7 : (Real.sqrt (y ^ 3 + y)) ^ 2 = y ^ 3 + y := Real.sq_sqrt (show 0 ≤ y ^ 3 + y by linarith)

  rw [eq4, eq5, eq6, eq7] at eq1

  have eq8 : Real.sqrt (x ^ 3 + y) * Real.sqrt (y ^ 3 + x) = Real.sqrt (x ^ 3 + x) * Real.sqrt (y ^ 3 + y) := by
    nlinarith [Real.sqrt_nonneg (x ^ 3 + y), Real.sqrt_nonneg (y ^ 3 + x), Real.sqrt_nonneg (x ^ 3 + x), Real.sqrt_nonneg (y ^ 3 + y), mul_nonneg (Real.sqrt_nonneg (x ^ 3 + y)) (Real.sqrt_nonneg (y ^ 3 + x)), mul_nonneg (Real.sqrt_nonneg (x ^ 3 + x)) (Real.sqrt_nonneg (y ^ 3 + y))]

  have eq9 : (Real.sqrt (x ^ 3 + y) * Real.sqrt (y ^ 3 + x)) ^ 2 = (Real.sqrt (x ^ 3 + x) * Real.sqrt (y ^ 3 + y))  ^ 2 := by 
    rw [eq8]

  have eq10 : (Real.sqrt (x ^ 3 + y) * Real.sqrt (y ^ 3 + x)) ^ 2 = (Real.sqrt (x ^ 3 + y)) ^ 2 * (Real.sqrt (y ^ 3 + x)) ^ 2 := by ring
  have eq11 : (Real.sqrt (x ^ 3 + x) * Real.sqrt (y ^ 3 + y))  ^ 2 = (Real.sqrt (x ^ 3 + x)) ^ 2 * (Real.sqrt (y ^ 3 + y)) ^ 2 := by ring

  rw [eq10, eq11] at eq9
  rw [eq4, eq5, eq6, eq7] at eq9

  have eq12 : (x - y) ^ 2 * (x  ^ 2 + x * y + y ^ 2) = 0 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y), mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ y by nlinarith)]

  cases' (mul_eq_zero.mp eq12) with eq13 eq14
  · -- Case (x - y) ^ 2 = 0 
    nlinarith 
  · -- Case x ^ 2 + x * y + y ^ 2 = 0 
    have eq15 : x ^ 2 + x * y + y ^ 2 = 0 := by 
      nlinarith
    have eq16 : x ^ 2 + y ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y)]

    have hx1 : x = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (y)]
    have hy1 : y = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (y)]

    linarith