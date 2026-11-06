import Mathlib

theorem algebra_326667 {m n : ℝ} (h₀ : m ≠ n) (h₁ : m^2 = m + 1) (h₂ : n^2 = n + 1) :
    m^5 + n^5 = 11 := by

  have h3 : m + n = 1 := by
    have h : m^2 - n^2 = m - n := by linarith
    have h4 : m - n ≠ 0 := by
      intro h'
      have h5 : m = n := by linarith
      contradiction
    have h5 : m + n = 1 := by
      apply (mul_left_inj' h4).mp
      linarith
    exact h5

  have eq1 : m^2 = m + 1 := h₁
  have eq2 : n^2 = n + 1 := h₂

  have eq3 : m^3 = 2 * m + 1 := by
    calc
      m^3 = m * m^2 := by ring
      _ = m * (m + 1) := by rw [eq1]
      _ = m^2 + m := by ring
      _ = (m + 1) + m := by rw [eq1]
      _ = 2 * m + 1 := by ring

  have eq4 : n^3 = 2 * n + 1 := by
    calc
      n^3 = n * n^2 := by ring
      _ = n * (n + 1) := by rw [eq2]
      _ = n^2 + n := by ring
      _ = (n + 1) + n := by rw [eq2]
      _ = 2 * n + 1 := by ring

  have eq5 : m^4 = 3 * m + 2 := by
    calc
      m^4 = m * m^3 := by ring
      _ = m * (2 * m + 1) := by rw [eq3]
      _ = 2 * m^2 + m := by ring
      _ = 2 * (m + 1) + m := by rw [eq1]
      _ = 2 * m + 2 + m := by ring
      _ = 3 * m + 2 := by ring

  have eq6 : n^4 = 3 * n + 2 := by
    calc
      n^4 = n * n^3 := by ring
      _ = n * (2 * n + 1) := by rw [eq4]
      _ = 2 * n^2 + n := by ring
      _ = 2 * (n + 1) + n := by rw [eq2]
      _ = 2 * n + 2 + n := by ring
      _ = 3 * n + 2 := by ring

  have eq7 : m^5 = 5 * m + 3 := by
    calc
      m^5 = m * m^4 := by ring
      _ = m * (3 * m + 2) := by rw [eq5]
      _ = 3 * m^2 + 2 * m := by ring
      _ = 3 * (m + 1) + 2 * m := by rw [eq1]
      _ = 3 * m + 3 + 2 * m := by ring
      _ = 5 * m + 3 := by ring

  have eq8 : n^5 = 5 * n + 3 := by
    calc
      n^5 = n * n^4 := by ring
      _ = n * (3 * n + 2) := by rw [eq6]
      _ = 3 * n^2 + 2 * n := by ring
      _ = 3 * (n + 1) + 2 * n := by rw [eq2]
      _ = 3 * n + 3 + 2 * n := by ring
      _ = 5 * n + 3 := by ring

  calc
    m^5 + n^5 = (5 * m + 3) + (5 * n + 3) := by rw [eq7, eq8]
    _ = 5 * (m + n) + 6 := by ring
    _ = 5 * (1) + 6 := by rw [h3]
    _ = 11 := by norm_num