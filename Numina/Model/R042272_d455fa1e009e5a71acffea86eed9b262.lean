import Mathlib

theorem inequalities_180276 (x : ℤ) (hx : x ≠ 13) : |(2 / (x - 13 : ℝ))| > 8 / 9 ↔ x = 11 ∨ x = 12 ∨ x = 14 ∨ x = 15 := by
  constructor
  · -- If |2/(x-13)| > 8/9, then x = 11,12,14,15.
    intro h
    have h1 : (x : ℝ) ≠ 13 := by exact_mod_cast (show x ≠ 13 by exact hx)
    have h2 : (x - 13 : ℝ) ≠ 0 := by
      intro h3
      have h4 : (x : ℝ) = 13 := by linarith
      tauto
    have h3 : |(2 / (x - 13 : ℝ))| > 8 / 9 := h
    have h4 : (2 / (x - 13 : ℝ)) > 8 / 9 ∨ (2 / (x - 13 : ℝ)) < -8 / 9 := by
      cases (abs_cases (2 / (x - 13 : ℝ))) with
      | inl h9 =>
        left
        linarith
      | inr h9 =>
        right
        linarith
    rcases h4 with h4 | h4
    · -- Case 2/(x-13) > 8/9
      have h5 : ((x - 13 : ℝ)) > 0 := by
        by_contra h6
        push_neg at h6
        have h7 : ((x - 13 : ℝ)) ≤ 0 := by nlinarith
        have h8 : (2 / (x - 13 : ℝ)) ≤ 0 := by
          apply div_nonpos_of_nonneg_of_nonpos
          · norm_num
          · linarith
        linarith
      have h6 : (2 / (x - 13 : ℝ)) > 8 / 9 := h4
      have h7 : ((x - 13 : ℝ)) > 0 := h5
      have h8 : (2 : ℝ) > (8 / 9) * (x - 13) := by
        have h9 : (2 / (x - 13 : ℝ)) > (8 / 9 : ℝ) := h4
        have h10 : (2 / (x - 13 : ℝ)) = (2 : ℝ) / (x - 13 : ℝ) := by ring
        rw [h10] at h9
        have h11 : (x - 13 : ℝ) > 0 := h5
        apply (lt_div_iff₀ (by linarith)).mp at h9
        linarith
      have h9 : (x : ℝ) < (61 / 4 : ℝ) := by
        nlinarith
      have h10 : (x : ℝ) > (13 : ℝ) := by linarith
      have h11 : x < 16 := by
        by_contra h15
        push_neg at h15
        have h16 : x ≥ 16 := by omega
        have h17 : (x : ℝ) ≥ (16 : ℝ) := by exact_mod_cast h16
        linarith
      have h12 : x > 13 := by
        by_contra h13
        push_neg at h13
        have h14 : x ≤ 13 := by omega
        have h15 : (x : ℝ) ≤ (13 : ℝ) := by exact_mod_cast h14
        linarith
      have h13 : x = 14 ∨ x = 15 := by
        omega
      rcases h13 with h14 | h15
      · -- x = 14
        simp [h14]
      · -- x = 15
        simp [h15]
    · -- Case 2/(x-13) < -8/9
      have h5 : ((x - 13 : ℝ)) < 0 := by
        by_contra h6
        push_neg at h6
        have h7 : ((x - 13 : ℝ)) ≥ 0 := by linarith
        have h8 : (2 / (x - 13 : ℝ)) ≥ 0 := by
          apply div_nonneg
          · norm_num
          · linarith
        linarith
      have h6 : (2 / (x - 13 : ℝ)) < -8 / 9 := h4
      have h7 : ((x - 13 : ℝ)) < 0 := h5
      have h8 : (2 * 9 : ℝ) > -8 * (x - 13) := by
        have h13 : (2 / (x - 13 : ℝ)) < (-8 / 9 : ℝ) := h4
        have h14 : (2 / (x - 13 : ℝ)) = (2 : ℝ) / (x - 13 : ℝ) := by ring
        rw [h14] at h13
        have h15 : (x - 13 : ℝ) < 0 := h5
        apply (div_lt_iff_of_neg' (by linarith)).mp at h13
        nlinarith
      have h9 : (x : ℝ) > (43 / 4 : ℝ) := by
        nlinarith
      have h10 : (x : ℝ) < (13 : ℝ) := by linarith
      have h11 : x > 10 := by
        by_contra h14
        push_neg at h14
        have h15 : x ≤ 10 := by omega
        have h16 : (x : ℝ) ≤ (10 : ℝ) := by exact_mod_cast h15
        nlinarith
      have h12 : x < 13 := by
        by_contra h13
        push_neg at h13
        have h14 : x ≥ 13 := by omega
        have h15 : (x : ℝ) ≥ (13 : ℝ) := by exact_mod_cast h14
        linarith
      have h13 : x = 11 ∨ x = 12 := by
        omega
      rcases h13 with h14 | h15
      · -- x = 11
        simp [h14]
      · -- x = 12
        simp [h15]
  · -- If x = 11,12,14,15 then |2/(x-13)| > 8/9.
    intro h
    rcases h with (rfl | rfl | rfl | rfl)
    · -- x = 11
      norm_num [abs_of_neg]
    · -- x = 12
      norm_num [abs_of_neg]
    · -- x = 14
      norm_num [abs_of_pos]
    · -- x = 15
      norm_num [abs_of_pos]