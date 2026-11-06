import Mathlib

theorem algebra_322606 {m n : ℝ} (hm : m ≠ n) (h1 : m^2 = m + 1) (h2 : n^2 = n + 1) :
    m^5 + n^5 = 11 := by

  have eq_m3 : m^3 = 2 * m + 1 := by
    calc
      m^3 = m * m^2 := by ring
      _ = m * (m + 1) := by rw [h1]
      _ = m^2 + m := by ring
      _ = (m + 1) + m := by rw [h1]
      _ = 2 * m + 1 := by ring

  have eq_n3 : n^3 = 2 * n + 1 := by
    calc
      n^3 = n * n^2 := by ring
      _ = n * (n + 1) := by rw [h2]
      _ = n^2 + n := by ring
      _ = (n + 1) + n := by rw [h2]
      _ = 2 * n + 1 := by ring

  have eq_m4 : m^4 = 3 * m + 2 := by
    calc
      m^4 = m * m^3 := by ring
      _ = m * (2 * m + 1) := by rw [eq_m3]
      _ = 2 * m^2 + m := by ring
      _ = 2 * (m + 1) + m := by rw [h1]
      _ = (2 * m + 2) + m := by ring
      _ = 3 * m + 2 := by ring

  have eq_n4 : n^4 = 3 * n + 2 := by
    calc
      n^4 = n * n^3 := by ring
      _ = n * (2 * n + 1) := by rw [eq_n3]
      _ = 2 * n^2 + n := by ring
      _ = 2 * (n + 1) + n := by rw [h2]
      _ = (2 * n + 2) + n := by ring
      _ = 3 * n + 2 := by ring

  have eq_m5 : m^5 = 5 * m + 3 := by
    calc
      m^5 = m * m^4 := by ring
      _ = m * (3 * m + 2) := by rw [eq_m4]
      _ = 3 * m^2 + 2 * m := by ring
      _ = 3 * (m + 1) + 2 * m := by rw [h1]
      _ = (3 * m + 3) + 2 * m := by ring
      _ = 5 * m + 3 := by ring

  have eq_n5 : n^5 = 5 * n + 3 := by
    calc
      n^5 = n * n^4 := by ring
      _ = n * (3 * n + 2) := by rw [eq_n4]
      _ = 3 * n^2 + 2 * n := by ring
      _ = 3 * (n + 1) + 2 * n := by rw [h2]
      _ = (3 * n + 3) + 2 * n := by ring
      _ = 5 * n + 3 := by ring

  have h3 : m + n = 1 := by
    have h4 : m^2 - n^2 = m - n := by linarith
    have h5 : (m - n) * (m + n) = m - n := by
      linarith [h4]
    have h6 : m - n ≠ 0 := by
      intro h
      apply hm
      linarith
    have h7 : (m + n) = 1 := by
      apply (mul_left_inj' h6).mp
      linarith
    linarith

  linarith [eq_m5, eq_n5, h3]