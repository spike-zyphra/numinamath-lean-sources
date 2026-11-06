import Mathlib

theorem algebra_299818 {m n : ℝ} (hm : m^2 = m + 1) (hn : n^2 = n + 1) (hmn : m ≠ n) :
    m^5 + n^5 = 11 := by 
  have h1 : m^2 - n^2 = m - n := by linarith
  have h2 : m^2 - n^2 = (m - n) * (m + n) := by 
    ring
  rw [h2] at h1
  have h3 : m + n = 1 := by 
    have h4 : m - n ≠ 0 := by 
      intro h
      apply hmn
      linarith
    apply (mul_left_inj' h4).mp 
    linarith
  have hm3 : m^3 = 2 * m + 1 := by
    calc
      m^3 = m * m^2 := by ring
      _   = m * (m + 1) := by rw [hm]
      _   = m^2 + m := by ring
      _   = (m + 1) + m := by rw [hm]
      _   = 2 * m + 1 := by ring
  have hm4 : m^4 = 3 * m + 2 := by 
    calc 
      m^4 = m * m^3 := by ring
      _   = m * (2 * m + 1) := by rw [hm3]
      _   = 2 * m^2 + m := by ring
      _   = 2 * (m + 1) + m := by rw [hm]
      _   = 2 * m + 2 + m := by ring
      _   = 3 * m + 2 := by ring
  have hm5 : m^5 = 5 * m + 3 := by 
    calc 
      m^5 = m * m^4 := by ring
      _   = m * (3 * m + 2) := by rw [hm4]
      _   = 3 * m^2 + 2 * m := by ring
      _   = 3 * (m + 1) + 2 * m := by rw [hm]
      _   = 3 * m + 3 + 2 * m := by ring
      _   = 5 * m + 3 := by ring
  have hn3 : n^3 = 2 * n + 1 := by
    calc
      n^3 = n * n^2 := by ring
      _   = n * (n + 1) := by rw [hn]
      _   = n^2 + n := by ring
      _   = (n + 1) + n := by rw [hn]
      _   = 2 * n + 1 := by ring
  have hn4 : n^4 = 3 * n + 2 := by 
    calc 
      n^4 = n * n^3 := by ring
      _   = n * (2 * n + 1) := by rw [hn3]
      _   = 2 * n^2 + n := by ring
      _   = 2 * (n + 1) + n := by rw [hn]
      _   = 2 * n + 2 + n := by ring
      _   = 3 * n + 2 := by ring
  have hn5 : n^5 = 5 * n + 3 := by 
    calc 
      n^5 = n * n^4 := by ring
      _   = n * (3 * n + 2) := by rw [hn4]
      _   = 3 * n^2 + 2 * n := by ring
      _   = 3 * (n + 1) + 2 * n := by rw [hn]
      _   = 3 * n + 3 + 2 * n := by ring
      _   = 5 * n + 3 := by ring
  calc 
    m^5 + n^5 = (5 * m + 3) + (5 * n + 3) := by rw [hm5, hn5]
    _         = 5 * (m + n) + 6 := by ring
    _         = 5 * 1 + 6 := by rw [h3]
    _         = 11 := by norm_num