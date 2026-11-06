import Mathlib

theorem algebra_322580 {m n : ℝ} (hmn : m ≠ n) (h1 : m^2 = m + 1) (h2 : n^2 = n + 1) :
    m^5 + n^5 = 11 := by
  have h3 : m^2 - n^2 = m - n := by linarith
  have h4 : (m - n) * (m + n) = m - n := by
    linarith [h3]
  have h5 : (m - n) * ((m + n) - 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case h6 : m - n = 0
    exfalso
    apply hmn
    linarith
  · -- Case h7 : (m + n) - 1 = 0
    have hmn1 : m + n = 1 := by linarith
    have eq1 : m^3 = 2 * m + 1 := by
      calc
        m^3 = m * m^2 := by ring
        _ = m * (m + 1) := by rw [h1]
        _ = m^2 + m := by ring
        _ = (m + 1) + m := by rw [h1]
        _ = 2 * m + 1 := by ring
    have eq2 : m^4 = 3 * m + 2 := by
      calc
        m^4 = (m^2) ^ 2 := by ring
        _ = (m + 1) ^ 2 := by rw [h1]
        _ = m^2 + 2 * m + 1 := by ring
        _ = (m + 1) + 2 * m + 1 := by rw [h1]
        _ = 3 * m + 2 := by ring
    have eq3 : m^5 = 5 * m + 3 := by
      calc
        m^5 = m * m^4 := by ring
        _ = m * (3 * m + 2) := by rw [eq2]
        _ = 3 * m^2 + 2 * m := by ring
        _ = 3 * (m + 1) + 2 * m := by rw [h1]
        _ = 5 * m + 3 := by ring
    have eq4 : n^3 = 2 * n + 1 := by
      calc
        n^3 = n * n^2 := by ring
        _ = n * (n + 1) := by rw [h2]
        _ = n^2 + n := by ring
        _ = (n + 1) + n := by rw [h2]
        _ = 2 * n + 1 := by ring
    have eq5 : n^4 = 3 * n + 2 := by
      calc
        n^4 = (n^2) ^ 2 := by ring
        _ = (n + 1) ^ 2 := by rw [h2]
        _ = n^2 + 2 * n + 1 := by ring
        _ = (n + 1) + 2 * n + 1 := by rw [h2]
        _ = 3 * n + 2 := by ring
    have eq6 : n^5 = 5 * n + 3 := by
      calc
        n^5 = n * n^4 := by ring
        _ = n * (3 * n + 2) := by rw [eq5]
        _ = 3 * n^2 + 2 * n := by ring
        _ = 3 * (n + 1) + 2 * n := by rw [h2]
        _ = 5 * n + 3 := by ring
    have eq7 : m^5 + n^5 = 5 * (m + n) + 6 := by
      linarith [eq3, eq6]
    rw [hmn1] at eq7
    linarith