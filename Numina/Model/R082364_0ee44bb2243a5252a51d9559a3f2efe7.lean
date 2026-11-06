import Mathlib

theorem algebra_298913 {m n : ℝ} (hmn : m ≠ n) (hm : m^2 = m + 1) (hn : n^2 = n + 1) :
    m^5 + n^5 = 11 := by
  have h1 : m^2 = m + 1 := hm
  have h2 : n^2 = n + 1 := hn

  have h3 : m^3 = 2 * m + 1 := by
    calc 
      m^3 = m * m^2 := by ring
      _   = m * (m + 1) := by rw [h1]
      _   = m^2 + m := by ring
      _   = (m + 1) + m := by rw [h1]
      _   = 2 * m + 1 := by ring

  have h4 : n^3 = 2 * n + 1 := by
    calc 
      n^3 = n * n^2 := by ring
      _   = n * (n + 1) := by rw [h2]
      _   = n^2 + n := by ring
      _   = (n + 1) + n := by rw [h2]
      _   = 2 * n + 1 := by ring

  have h5 : m^4 = 3 * m + 2 := by
    calc 
      m^4 = m * m^3 := by ring
      _   = m * (2 * m + 1) := by rw [h3]
      _   = 2 * m^2 + m := by ring
      _   = 2 * (m + 1) + m := by rw [h1]
      _   = 3 * m + 2 := by ring

  have h6 : n^4 = 3 * n + 2 := by
    calc 
      n^4 = n * n^3 := by ring
      _   = n * (2 * n + 1) := by rw [h4]
      _   = 2 * n^2 + n := by ring
      _   = 2 * (n + 1) + n := by rw [h2]
      _   = 3 * n + 2 := by ring

  have h7 : m^5 = 5 * m + 3 := by
    calc 
      m^5 = m * m^4 := by ring
      _   = m * (3 * m + 2) := by rw [h5]
      _   = 3 * m^2 + 2 * m := by ring
      _   = 3 * (m + 1) + 2 * m := by rw [h1]
      _   = 5 * m + 3 := by ring

  have h8 : n^5 = 5 * n + 3 := by
    calc 
      n^5 = n * n^4 := by ring
      _   = n * (3 * n + 2) := by rw [h6]
      _   = 3 * n^2 + 2 * n := by ring
      _   = 3 * (n + 1) + 2 * n := by rw [h2]
      _   = 5 * n + 3 := by ring

  have h9 : m + n = 1 := by
    have h10 : m^2 - n^2 = (m + 1) - (n + 1) := by linarith [h1, h2]
    have h11 : m^2 - n^2 = (m - n) * (m + n) := by ring
    rw [h11] at h10
    have h12 : m - n ≠ 0 := sub_ne_zero_of_ne hmn
    have h13 : m + n = 1 := by 
      apply (mul_left_inj' h12).mp 
      linarith
    exact h13
  
  linarith [h7, h8, h9]