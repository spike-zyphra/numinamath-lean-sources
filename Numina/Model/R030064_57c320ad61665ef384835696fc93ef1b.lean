import Mathlib

theorem inequalities_174231 (a : ℕ) :
    1 / 4 < a / (a + 12 : ℚ) ∧ a / (a + 12 : ℚ) < 1 / 3 ↔ a = 5 := by
  constructor
  · -- Assume both inequalities hold, prove a = 5
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : a > 0 := by
      by_contra h3
      push_neg at h3
      have h4 : a = 0 := by
        omega
      rw [h4] at h1 h2
      norm_num at h1 h2
    have h4 : (a : ℚ) > (0 : ℚ) := by
      exact_mod_cast h3
    have h5 : (a : ℚ) > (4 : ℚ) := by
      have h6 : (1 : ℚ) / 4 < (a : ℚ) / (a + 12 : ℚ) := h1
      have pos1 : (a + 12 : ℚ) > 0 := by
        have h3' : (a : ℚ) > (0 : ℚ) := h4
        linarith
      have h7 : (1 : ℚ) / 4 < (a : ℚ) / (a + 12 : ℚ) := h1
      have h8 : (1 : ℚ) * (a + 12 : ℚ) < (4 : ℚ) * (a : ℚ) := by
        have h9 : (4 : ℚ) * (a : ℚ) > 0 := by
          nlinarith [show (a : ℚ) > 0 from h4]
        have h7' : (1 : ℚ) / 4 < (a : ℚ) / (a + 12 : ℚ) := h1
        have h11 : (1 : ℚ) / 4 - (a : ℚ) / (a + 12 : ℚ) < 0 := by linarith
        have h12 : (1 : ℚ) / 4 - (a : ℚ) / (a + 12 : ℚ) = ( (1 * (a + 12) - 4 * a ) / (4 * (a + 12) ) ) := by
          field_simp
          <;> ring
        rw [h12] at h11
        have pos2 : (4 * (a + 12) : ℚ) > 0 := by
          nlinarith [show (a : ℚ) > 0 by assumption, show (a + 12 : ℚ) > 0 by linarith]
        apply (div_lt_iff₀ pos2).mp at h11
        linarith
      linarith
    have h6 : (a : ℚ) < (6 : ℚ) := by
      have h7 : (a : ℚ) / (a + 12 : ℚ) < (1 : ℚ) / 3 := h2
      have pos1 : (a + 12 : ℚ) > 0 := by
        have h3' : (a : ℚ) > (0 : ℚ) := h4
        linarith
      have h8 : (3 : ℚ) * (a : ℚ) < (1 : ℚ) * (a + 12 : ℚ) := by
        have h7' : (a : ℚ) / (a + 12 : ℚ) < (1 : ℚ) / 3 := h2
        have h11 : (a : ℚ) / (a + 12 : ℚ) - (1 : ℚ) / 3 < 0 := by linarith
        have h12 : (a : ℚ) / (a + 12 : ℚ) - (1 : ℚ) / 3 = ( (3 * a - 1 * (a + 12) ) / (3 * (a + 12) ) ) := by
          field_simp
          <;> ring
        rw [h12] at h11
        have pos2 : (3 * (a + 12 : ℚ) ) > 0 := by
          nlinarith [show (a : ℚ) > 0 by assumption, show (a + 12 : ℚ) > 0 by linarith]
        apply (div_lt_iff₀ pos2).mp at h11
        linarith
      linarith
    have h7 : a > 4 := by
      by_contra h7
      push_neg at h7
      have h8 : a ≤ 4 := by
        omega
      have h9 : (a : ℚ) ≤ (4 : ℚ) := by
        exact_mod_cast h8
      nlinarith
    have h8 : a < 6 := by
      by_contra h8
      push_neg at h8
      have h9 : a ≥ 6 := by
        omega
      have h10 : (a : ℚ) ≥ (6 : ℚ) := by
        exact_mod_cast h9
      nlinarith
    have h9 : a = 5 := by
      omega
    exact_mod_cast h9
  · -- Assume a = 5, prove both inequalities
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num