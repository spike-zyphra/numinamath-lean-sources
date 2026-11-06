import Mathlib

theorem algebra_178110 {b g : ℕ} (hb : b ≠ 0) (hg : g ≠ 0)
    (h1 : (1 / 6 : ℚ) * b + (1 / 7 : ℚ) * g = 48 + 50)
    (h2 : (1 - (1 / 6 : ℚ) - (1 / 7 : ℚ)) * g = 2 * (1 - (1 / 6 : ℚ) - (1 / 7 : ℚ)) * b) :
    b = 72 ∧ g = 72 := by
  have h3 : (b : ℚ) > 0 := by exact_mod_cast (show 0 < b by omega)
  have h4 : (g : ℚ) > 0 := by exact_mod_cast (show 0 < g by omega)
  have h5 : (7 : ℚ) * (b : ℚ) + 6 * (g : ℚ) = 4116 := by
    have h6 : (1 / 6 : ℚ) * b + (1 / 7 : ℚ) * g = 98 := by
      linarith
    linarith [h6]
  have h8 : (29 : ℚ) * (g : ℚ) = 2 * (29 : ℚ) * (b : ℚ) := by
    have h9 : (1 - (1 / 6 : ℚ) - (1 / 7 : ℚ)) * g = 2 * (1 - (1 / 6 : ℚ) - (1 / 7 : ℚ)) * b := h2
    norm_num at h9 ⊢
    linarith
  have h10 : (g : ℚ) = 2 * (b : ℚ) := by
    have h11 : (29 : ℚ) ≠ 0 := by norm_num
    have h12 : (29 : ℚ) * (g : ℚ) = 2 * (29 : ℚ) * (b : ℚ) := h8
    have h13 : (g : ℚ) = 2 * (b : ℚ) := by
      apply (mul_left_inj' h11).mp
      linarith
    exact h13
  rw [h10] at h5
  have h14 : (19 : ℚ) * (b : ℚ) = 4116 := by 
    linarith
  have h15 : (b : ℚ) = 4116 / 19 := by
    field_simp
    linarith
  have h16 : b = 72 := by
    have h19 : (b : ℚ) * 19 = 4116 := by
      linarith [h14]
    have h20 : b * 19 = 4116 := by
      exact_mod_cast h19
    omega
  have h17 : g = 72 := by
    have h18 : (g : ℚ) = 2 * (b : ℚ) := h10
    have h19 : (b : ℚ) = 72 := by
      exact_mod_cast h16
    have h20 : (g : ℚ) = 72 := by
      rw [h19] at h18
      norm_num at h18 ⊢
      linarith
    exact_mod_cast h20
  exact ⟨h16, h17⟩