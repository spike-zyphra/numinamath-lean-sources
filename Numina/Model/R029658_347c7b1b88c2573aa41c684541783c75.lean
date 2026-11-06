import Mathlib

theorem algebra_450 : IsLeast {x + y | (x : ℕ) (y : ℕ) (hy : 2011 ≤ y) (h : (x - 2011 : ℚ) / (y + 2011) = 1 / 2011)} 4024 := by
  constructor
  · -- Show 4024 in the set.
    use 2013, 2011
    norm_num
  · -- Show there is no smaller element in the set.
    intro z hz
    rcases hz with ⟨x, y, hy, h, hz⟩
    have h2 : (y : ℚ) ≥ (2011 : ℚ) := by
      exact_mod_cast hy
    have h4 : (x - 2011 : ℚ) / (y + 2011 : ℚ) = (1 : ℚ) / (2011 : ℚ) := by
      linarith [h]
    have h5 : (x - 2011 : ℚ) / (y + 2011 : ℚ) = (1 : ℚ) / (2011 : ℚ) := h4
    have h6 : (y : ℚ) + (2011 : ℚ) > 0 := by
      have h7 : (y : ℚ) ≥ (2011 : ℚ) := by
        exact_mod_cast hy
      linarith
    have h7 : (x - 2011 : ℚ) * (2011 : ℚ) = (1 : ℚ) * ((y + 2011) : ℚ) := by
      field_simp at h5 ⊢
      nlinarith
    have h9 : (2011 : ℚ) * (x : ℚ) - (2011 : ℚ) * (2011 : ℚ) = (y : ℚ) + (2011 : ℚ) := by
      nlinarith [h7]
    have h10 : (2011 : ℕ) * (x : ℕ) = (y + 2011 * 2012) := by
      have h12 : (2011 : ℚ) * (x : ℚ) = (y + 2011 * 2012) := by
        nlinarith [h9]
      exact_mod_cast h12
    omega