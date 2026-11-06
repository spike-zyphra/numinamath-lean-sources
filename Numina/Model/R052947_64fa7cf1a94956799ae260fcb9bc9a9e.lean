import Mathlib

theorem algebra_3819 {x : ℂ} (hx : x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0) :
    x ^ 40 + x ^ 30 + x ^ 20 + x ^ 10 + 1 = 5 := by
  have h2 : x ≠ 0 := by
    by_contra h
    rw [h] at hx
    norm_num at hx
  have h3 : x ≠ 1 := by
    by_contra h
    rw [h] at hx
    norm_num at hx
  have h4 : x ^ 5 - 1 = 0 := by
    have h5 : x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = 0 := hx
    have h6 : (x - 1) * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) = 0 := by
      rw [h5]
      norm_num
    have h7 : (x - 1) * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) = x ^ 5 - 1 := by
      ring
    rw [h7] at h6
    exact h6
  have h5 : x ^ 5 = 1 := by
    have h8 : x ^ 5 - 1 = 0 := h4
    have h9 : x ^ 5 = 1 := by
      have eq : x ^ 5 - 1 = 0 := h8
      have h10 : x ^ 5 = 1 := by
        calc
          x ^ 5 = (x ^ 5 - 1) + 1 := by ring_nf
          _ = 0 + 1 := by rw [eq]
          _ = 1 := by ring
      exact h10
    exact h9
  have h2 : x ^ 10 = 1 := by
    calc
      x ^ 10 = (x ^ 5) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [h5]
      _ = 1 := by norm_num
  have h3 : x ^ 20 = 1 := by
    calc
      x ^ 20 = (x ^ 5) ^ 4 := by ring
      _ = 1 ^ 4 := by rw [h5]
      _ = 1 := by norm_num
  have h4 : x ^ 30 = 1 := by
    calc
      x ^ 30 = (x ^ 5) ^ 6 := by ring
      _ = 1 ^ 6 := by rw [h5]
      _ = 1 := by norm_num
  have h6 : x ^ 40 = 1 := by
    calc
      x ^ 40 = (x ^ 5) ^ 8 := by ring
      _ = 1 ^ 8 := by rw [h5]
      _ = 1 := by norm_num
  rw [h6, h4, h3, h2]
  norm_num