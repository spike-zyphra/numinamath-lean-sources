import Mathlib

theorem algebra_289734 {x y m n : ℤ} (hy : x > y) (hxy : x + y = 7 ∧ x * y = 12)
    (hn : m > n) (hm : m + n = 13 ∧ m ^ 2 + n ^ 2 = 97) :
    (x - y) - (m - n) = -4 := by
  have h1 : x + y = 7 := hxy.1
  have h2 : x * y = 12 := hxy.2

  have h3 : x = 4 := by
    have h4 : y = 7 - x := by linarith
    rw [h4] at h2
    have h5 : x^2 - 7 * x + 12 = 0 := by
      linarith
    have h6 : (x - 3) * (x - 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- x = 3
      have hx : x = 3 := by linarith
      have hy' : y = 4 := by linarith
      linarith -- contradiction since x < y
    · -- x = 4
      have hx : x = 4 := by linarith
      exact hx
  have hy' : y = 3 := by linarith
  have h4 : m + n = 13 := hm.1
  have h5 : m^2 + n^2 = 97 := hm.2
  have hmn : m * n = 36 := by
    have h6 : (m + n)^2 = m^2 + 2 * (m * n) + n^2 := by ring
    rw [h4] at h6
    nlinarith
  have h6 : m - n = 5 := by
    have h7 : n = 13 - m := by linarith
    rw [h7] at hmn
    have h8 : m^2 - 13 * m + 36 = 0 := by
      nlinarith
    have h9 : (m - 4) * (m - 9) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- m = 4
      have hm' : m = 4 := by linarith
      have hn' : n = 9 := by linarith
      linarith -- contradiction since m < n
    · -- m = 9
      have hm' : m = 9 := by linarith
      have hn' : n = 4 := by linarith
      linarith
  have hA : x - y = 1 := by
    rw [h3, hy']
    all_goals linarith
  have hB : m - n = 5 := by
    linarith [h6]
  linarith [hA, hB]