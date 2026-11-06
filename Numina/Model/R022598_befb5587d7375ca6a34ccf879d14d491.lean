import Mathlib

theorem algebra_93964 {x y z a b c : ℝ} (h₀ : x * y / (x + y) = a) (h₁ : x * z / (x + z) = b)
    (h₂ : y * z / (y + z) = c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    x = 2 * a * b * c / (a * c + b * c - a * b) := by

  have h3 : x + y ≠ 0 := by
    by_contra h
    have h4 : x * y / (x + y) = 0 := by
      rw [h]
      norm_num
    have h5 : a = 0 := by linarith [h4, h₀]
    contradiction

  have h4 : x + z ≠ 0 := by
    by_contra h
    have h5 : x * z / (x + z) = 0 := by
      rw [h]
      norm_num
    have h6 : b = 0 := by linarith [h5, h₁]
    contradiction

  have h5 : y + z ≠ 0 := by
    by_contra h
    have h6 : y * z / (y + z) = 0 := by
      rw [h]
      norm_num
    have h7 : c = 0 := by linarith [h6, h₂]
    contradiction

  have hx1 : x ≠ 0 := by
    by_contra h
    have h0' : x * y / (x + y) = 0 := by
      rw [h]
      norm_num
    have ha0 : a = 0 := by linarith [h0', h₀]
    contradiction

  have hy1 : y ≠ 0 := by
    by_contra h
    have h0' : x * y / (x + y) = 0 := by
      rw [h]
      norm_num
    have ha0 : a = 0 := by linarith [h0', h₀]
    contradiction

  have hz1 : z ≠ 0 := by
    by_contra h
    have h1' : x * z / (x + z) = 0 := by
      rw [h]
      norm_num
    have hb0 : b = 0 := by linarith [h1', h₁]
    contradiction

  have eq1 : 1 / a = 1 / x + 1 / y := by
    have h6 : x * y = a * (x + y) := by
      have h7 : x + y ≠ 0 := h3
      field_simp at h₀ ⊢
      nlinarith
    have h8 : x ≠ 0 := hx1
    have h9 : y ≠ 0 := hy1
    field_simp [show x ≠ 0 by exact h8, show y ≠ 0 by exact h9, show a ≠ 0 by exact ha]
    nlinarith

  have eq2 : 1 / b = 1 / x + 1 / z := by
    have h7 : x * z = b * (x + z) := by
      have h8 : x + z ≠ 0 := h4
      field_simp at h₁ ⊢
      nlinarith
    have h8 : x ≠ 0 := hx1
    have h9 : z ≠ 0 := hz1
    field_simp [show x ≠ 0 by exact h8, show z ≠ 0 by exact h9, show b ≠ 0 by exact hb]
    nlinarith

  have eq3 : 1 / c = 1 / y + 1 / z := by
    have h10 : y * z = c * (y + z) := by
      have h11 : y + z ≠ 0 := h5
      field_simp at h₂ ⊢
      nlinarith
    have h12 : y ≠ 0 := hy1
    have h13 : z ≠ 0 := hz1
    field_simp [show y ≠ 0 by exact h12, show z ≠ 0 by exact h13, show c ≠ 0 by exact hc]
    nlinarith

  have eq4 : 1 / x = (1 / a + 1 / b - 1 / c) / 2 := by
    linarith [eq1, eq2, eq3]

  have h3 : a * c + b * c - a * b ≠ 0 := by
    by_contra h
    have h4 : 1 / x = 0 := by
      have eq4' : 1 / x = (1 / a + 1 / b - 1 / c) / 2 := eq4
      have eq4'' : (1 / a + 1 / b - 1 / c) = 0 := by
        have h4' : (1 / a + 1 / b - 1 / c) = ( (b * c + a * c - a * b) / (a * b * c) ) := by
          field_simp [ha, hb, hc]
          all_goals ring
        rw [h4']
        have h7 : b * c + a * c - a * b = 0 := by
          linarith [h]
        rw [h7]
        norm_num
      linarith
    have h0 : x ≠ 0 := hx1
    field_simp at h4

  have eq5 : x = 2 * a * b * c / (a * c + b * c - a * b) := by
    have eq6 : 1 / x = (1 / a + 1 / b - 1 / c) / 2 := eq4
    have eq7 : (b * c + a * c - a * b) * x = 2 * (a * b * c) := by
      have eq7' : 1 / x = (1 / a + 1 / b - 1 / c) / 2 := eq6
      field_simp [show x ≠ 0 by exact hx1, ha, hb, hc] at eq7' ⊢
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc]
    have h11 : a * c + b * c - a * b ≠ 0 := h3
    have h13 : a * b * c ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha
      exact hb
      exact hc
    field_simp [h11] at eq7 ⊢
    nlinarith

  exact eq5