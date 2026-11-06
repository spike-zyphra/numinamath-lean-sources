import Mathlib

theorem algebra_1050 (x y z : ℚ) (hxy : x * y * z < 0) (hsum : x + y + z > 0)
    (a : ℚ) (ha : a = -(x / abs x + y / abs y + z / abs z)) :
    ∑ i ∈ Finset.range 1001, a ^ (i + 1) = -1 := by
  have hx1 : x ≠ 0 := by
    by_contra h
    rw [h] at hxy
    nlinarith
  have hy1 : y ≠ 0 := by
    by_contra h
    rw [h] at hxy
    nlinarith
  have hz1 : z ≠ 0 := by
    by_contra h
    rw [h] at hxy
    nlinarith
  have h4 : a = -1 := by
    rw [ha]
    have h5 : x / abs x + y / abs y + z / abs z = 1 := by
      have h4 : (x > 0) ∧ (y > 0) ∧ (z < 0) ∨ (x > 0) ∧ (y < 0) ∧ (z > 0) ∨ (x < 0) ∧ (y > 0) ∧ (z > 0) := by
        have h1 : x * y * z < 0 := hxy
        have hx2 : x > 0 ∨ x < 0 := by
          by_contra h
          push_neg at h
          have h2 : x = 0 := by linarith
          contradiction
        cases hx2 with
        | inl hx_pos =>
          have h2 : y * z < 0 := by
            nlinarith
          have hy2 : y > 0 ∨ y < 0 := by
            by_contra h
            push_neg at h
            have h2 : y = 0 := by linarith
            contradiction
          cases hy2 with
          | inl hy_pos =>
            have h3 : z < 0 := by
              nlinarith
            left
            constructor
            · exact hx_pos
            constructor
            · exact hy_pos
            · linarith
          | inr hy_neg =>
            have h3 : z > 0 := by
              nlinarith
            right
            left
            constructor
            · exact hx_pos
            constructor
            · linarith
            · exact h3
        | inr hx_neg =>
          have h2 : y * z > 0 := by
            nlinarith
          have hy2 : y > 0 ∨ y < 0 := by
            by_contra h
            push_neg at h
            have h2 : y = 0 := by linarith
            contradiction
          cases hy2 with
          | inl hy_pos =>
            have h3 : z > 0 := by
              nlinarith
            right
            right
            constructor
            · linarith
            constructor
            · exact hy_pos
            · exact h3
          | inr hy_neg =>
            have h3 : z < 0 := by
              nlinarith
            exfalso
            nlinarith [show x + y + z ≤ 0 by linarith]
      rcases h4 with (h | h | h)
      · -- Case where x > 0, y > 0, z < 0
        have hx_abs : x / abs x = 1 := by
          have : abs x = x := by
            rw [abs_of_pos h.1]
          field_simp [this]
        have hy_abs : y / abs y = 1 := by
          have : abs y = y := by
            rw [abs_of_pos h.2.1]
          field_simp [this]
        have hz_abs : z / abs z = -1 := by
          have : abs z = -z := by
            rw [abs_of_neg h.2.2]
          field_simp [this]
        linarith [hx_abs, hy_abs, hz_abs]
      · -- Case where x > 0, y < 0, z > 0
        have hx_abs : x / abs x = 1 := by
          have : abs x = x := by
            rw [abs_of_pos h.1]
          field_simp [this]
        have hy_abs : y / abs y = -1 := by
          have : abs y = -y := by
            rw [abs_of_neg h.2.1]
          field_simp [this]
        have hz_abs : z / abs z = 1 := by
          have : abs z = z := by
            rw [abs_of_pos h.2.2]
          field_simp [this]
        linarith [hx_abs, hy_abs, hz_abs]
      · -- Case where x < 0, y > 0, z > 0
        have hx_abs : x / abs x = -1 := by
          have : abs x = -x := by
            rw [abs_of_neg h.1]
          field_simp [this]
        have hy_abs : y / abs y = 1 := by
          have : abs y = y := by
            rw [abs_of_pos h.2.1]
          field_simp [this]
        have hz_abs : z / abs z = 1 := by
          have : abs z = z := by
            rw [abs_of_pos h.2.2]
          field_simp [this]
        linarith [hx_abs, hy_abs, hz_abs]
    linarith [h5]
  rw [h4]
  norm_num [Finset.sum_range_succ]