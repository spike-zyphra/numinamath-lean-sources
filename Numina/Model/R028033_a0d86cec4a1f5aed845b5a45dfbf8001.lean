import Mathlib

theorem algebra_305597 {x y z : ℝ} (h₀ : x ≠ y) (h₁ : x ≠ z) (h₂ : y ≠ z)
    (h₃ : x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) = y + (x * z - y ^ 2) / (y ^ 2 + x ^ 2 + z ^ 2))
    (h₄ : x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) = z + (x * y - z ^ 2) / (z ^ 2 + x ^ 2 + y ^ 2))
    (h₅ : x + y + z = 1) :
    x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) = 0 := by

  have h6 : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 := by
    by_contra h
    have h7 : x ^ 2 + y ^ 2 + z ^ 2 = 0 := by
      linarith
    have hx1 : x ^ 2 ≥ 0 := sq_nonneg x
    have hy1 : y ^ 2 ≥ 0 := sq_nonneg y
    have hz1 : z ^ 2 ≥ 0 := sq_nonneg z
    have hx0 : x ^ 2 = 0 := by
      nlinarith
    have hy0 : y ^ 2 = 0 := by
      nlinarith
    have hz0 : z ^ 2 = 0 := by
      nlinarith
    have hx2 : x = 0 := by
      rw [sq_eq_zero_iff] at hx0
      exact hx0
    have hy2 : y = 0 := by
      rw [sq_eq_zero_iff] at hy0
      exact hy0
    have hz2 : z = 0 := by
      rw [sq_eq_zero_iff] at hz0
      exact hz0
    have h8 : x + y + z = 0 := by
      linarith [hx2, hy2, hz2]
    linarith [h8, h₅]

  have eq1 : (x - y) * (x ^ 2 + y ^ 2 + z ^ 2 - (x + y + z)) = 0 := by
    have eq2 : x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) = y + (x * z - y ^ 2) / (y ^ 2 + x ^ 2 + z ^ 2) := by
      linarith [h₃]
    have eq3 : (x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)) * (x ^ 2 + y ^ 2 + z ^ 2) = (y + (x * z - y ^ 2) / (y ^ 2 + x ^ 2 + z ^ 2)) * (x ^ 2 + y ^ 2 + z ^ 2) := by
      rw [eq2]
    have eq4 : (x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)) * (x ^ 2 + y ^ 2 + z ^ 2) = x * (x ^ 2 + y ^ 2 + z ^ 2) + (y * z - x ^ 2) := by
      field_simp [show x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 by exact h6]
    have eq5 : (y + (x * z - y ^ 2) / (y ^ 2 + x ^ 2 + z ^ 2)) * (x ^ 2 + y ^ 2 + z ^ 2) = y * (x ^ 2 + y ^ 2 + z ^ 2) + (x * z - y ^ 2) := by
      have h7 : y ^ 2 + x ^ 2 + z ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by ring
      rw [h7]
      field_simp [show x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 by exact h6]
    rw [eq4, eq5] at eq3
    nlinarith

  have eq2 : (x - z) * (x ^ 2 + y ^ 2 + z ^ 2 - (x + y + z)) = 0 := by
    have eq3 : x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) = z + (x * y - z ^ 2) / (z ^ 2 + x ^ 2 + y ^ 2) := by
      linarith [h₄]
    have eq4 : (x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)) * (x ^ 2 + y ^ 2 + z ^ 2) = (z + (x * y - z ^ 2) / (z ^ 2 + x ^ 2 + y ^ 2)) * (x ^ 2 + y ^ 2 + z ^ 2) := by
      rw [eq3]
    have eq5 : (x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)) * (x ^ 2 + y ^ 2 + z ^ 2) = x * (x ^ 2 + y ^ 2 + z ^ 2) + (y * z - x ^ 2) := by
      field_simp [show x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 by exact h6]
    have eq6 : (z + (x * y - z ^ 2) / (z ^ 2 + x ^ 2 + y ^ 2)) * (x ^ 2 + y ^ 2 + z ^ 2) = z * (x ^ 2 + y ^ 2 + z ^ 2) + (x * y - z ^ 2) := by
      have h7 : z ^ 2 + x ^ 2 + y ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by ring
      rw [h7]
      field_simp [show x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 by exact h6]
    rw [eq5, eq6] at eq4
    nlinarith

  have eq3 : x ^ 2 + y ^ 2 + z ^ 2 = 1 := by
    have h7 : (x - y) * (x ^ 2 + y ^ 2 + z ^ 2 - (x + y + z)) = 0 := by
      linarith [eq1]
    cases' (mul_eq_zero.1 h7) with h8 h9
    · 
      exfalso
      apply h₀
      linarith
    · 
      have h7' : x ^ 2 + y ^ 2 + z ^ 2 = x + y + z := by
        nlinarith
      have h7'' : x ^ 2 + y ^ 2 + z ^ 2 = 1 := by
        nlinarith [h₅, h7']
      linarith

  have h7 : x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) = 0 := by
    have h9 : x * (x ^ 2 + y ^ 2 + z ^ 2) + (y * z - x ^ 2) = 0 := by
      have eq4 : (x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)) * (x ^ 2 + y ^ 2 + z ^ 2) = x * (x ^ 2 + y ^ 2 + z ^ 2) + (y * z - x ^ 2) := by
        field_simp [show x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 by exact h6]
      have eq5 : (x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)) * (x ^ 2 + y ^ 2 + z ^ 2) = 0 := by
        have h10 : (x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2)) * (x ^ 2 + y ^ 2 + z ^ 2) = (x * (x ^ 2 + y ^ 2 + z ^ 2) + (y * z - x ^ 2)) := by
          field_simp [show x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 by exact h6]
        nlinarith [sq_pos_of_ne_zero (show (x-y) ≠ 0 by intro h; apply h₀; linarith), sq_pos_of_ne_zero (show (x-z) ≠ 0 by intro h; apply h₁; linarith), sq_pos_of_ne_zero (show (y-z) ≠ 0 by intro h; apply h₂; linarith), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), show x ^ 2 + y ^ 2 + z ^ 2 = 1 by linarith [eq3]]
      nlinarith
    have h11 : x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) = 0 := by
      have eq8 : x + (y * z - x ^ 2) / (x ^ 2 + y ^ 2 + z ^ 2) = (x * (x ^ 2 + y ^ 2 + z ^ 2) + (y * z - x ^ 2)) / (x ^ 2 + y ^ 2 + z ^ 2) := by
        field_simp [show x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 by exact h6]
      rw [eq8]
      have h13 : (x * (x ^ 2 + y ^ 2 + z ^ 2) + (y * z - x ^ 2)) / (x ^ 2 + y ^ 2 + z ^ 2) = 0 := by
        have h12 : x * (x ^ 2 + y ^ 2 + z ^ 2) + (y * z - x ^ 2) = 0 := h9
        rw [h12]
        norm_num
      linarith [h13]
    exact h11

  linarith [h7]