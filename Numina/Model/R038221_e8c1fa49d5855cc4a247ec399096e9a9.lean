import Mathlib

theorem algebra_607940 (F : ℝ → ℝ) (hF : Monotone F) (h1 : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → F (x / 3) = F x / 2) (h2 : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → F (1 - x) = 1 - F x) : F (173 / 1993) = 3 / 16 ∧ F (1 / 13) = 1 / 7 := by

  have h3 : F 0 = 0 := by
    have h3a : F (0 / 3) = F 0 / 2 := h1 0 (by constructor <;> norm_num)
    norm_num at h3a
    linarith

  have h4 : F 1 = 1 := by
    have h4a : F (1 - 1) = 1 - F 1 := h2 1 (by constructor <;> norm_num)
    have h3b : F 0 = 0 := h3
    norm_num at h4a h3b ⊢
    linarith

  have h5 : F (1 / 3) = 1 / 2 := by
    have h5a : F (1 / 3) = F 1 / 2 := by
      specialize h1 1 (by constructor <;> norm_num)
      norm_num at h1 ⊢
      linarith
    rw [h4] at h5a
    linarith

  have h6 : F (2 / 3) = 1 / 2 := by
    have h6a : F (1 - (1 / 3)) = 1 - F (1 / 3) := h2 (1 / 3) (by constructor <;> norm_num)
    have h5b : F (1 / 3) = 1 / 2 := h5
    norm_num at h6a ⊢
    linarith [h5b]

  have h7 : ∀ x : ℝ, 1 / 3 ≤ x ∧ x ≤ 2 / 3 → F x = 1 / 2 := by
    intro x hx
    have h8 : F x ≥ 1 / 2 := by
      have h9 : F (1 / 3) = 1 / 2 := h5
      have h10 : F (1 / 3) ≤ F x := by
        apply hF
        linarith [hx.1, hx.2]
      linarith [h9]
    have h11 : F x ≤ 1 / 2 := by
      have h12 : F (2 / 3) = 1 / 2 := h6
      have h13 : F x ≤ F (2 / 3) := by
        apply hF
        linarith [hx.1, hx.2]
      linarith [h12]
    linarith

  have h10 : F (173 / 1993) = 3 / 16 := by
    have h11 : F (173 / 1993) = F (519 / 1993) / 2 := by
      have h11a : F ((519 / 1993 : ℝ) / 3) = F (519 / 1993) / 2 := h1 (519 / 1993) (by constructor <;> norm_num)
      have h11b : (519 / 1993 : ℝ) / 3 = (173 / 1993 : ℝ) := by
        norm_num
      rw [h11b] at h11a
      linarith
    have h12 : F (519 / 1993) = F (1557 / 1993) / 2 := by
      have h12a : F ((1557 / 1993 : ℝ) / 3) = F (1557 / 1993) / 2 := h1 (1557 / 1993) (by constructor <;> norm_num)
      have h12b : (1557 / 1993 : ℝ) / 3 = (519 / 1993 : ℝ) := by
        norm_num
      rw [h12b] at h12a
      linarith
    have h13 : F (436 / 1993) = 1 - F (1557 / 1993) := by
      have h13a : F (1 - (1557 / 1993 : ℝ)) = 1 - F (1557 / 1993) := h2 (1557 / 1993) (by constructor <;> norm_num)
      have h13b : (1 - (1557 / 1993 : ℝ)) = (436 / 1993 : ℝ) := by
        norm_num
      rw [h13b] at h13a
      linarith
    have h14 : F (436 / 1993) = F (1308 / 1993) / 2 := by
      have h14a : F ((1308 / 1993 : ℝ) / 3) = F (1308 / 1993) / 2 := h1 (1308 / 1993) (by constructor <;> norm_num)
      have h14b : (1308 / 1993 : ℝ) / 3 = (436 / 1993 : ℝ) := by
        norm_num
      rw [h14b] at h14a
      linarith
    have h15 : F (685 / 1993) = 1 - F (1308 / 1993) := by
      have h15a : F (1 - (1308 / 1993 : ℝ)) = 1 - F (1308 / 1993) := h2 (1308 / 1993) (by constructor <;> norm_num)
      have h15b : (1 - (1308 / 1993 : ℝ)) = (685 / 1993 : ℝ) := by
        norm_num
      rw [h15b] at h15a
      linarith
    have h16 : F (685 / 1993) = 1 / 2 := by
      apply h7
      constructor <;> norm_num
    linarith

  have h17 : F (1 / 13) = 1 / 7 := by
    have h18 : F (1 / 13) = F (3 / 13) / 2 := by
      have h18a : F ((3 / 13 : ℝ) / 3) = F (3 / 13) / 2 := h1 (3 / 13) (by constructor <;> norm_num)
      have h18b : (3 / 13 : ℝ) / 3 = (1 / 13 : ℝ) := by
        norm_num
      rw [h18b] at h18a
      linarith
    have h19 : F (3 / 13) = F (9 / 13) / 2 := by
      have h19a : F ((9 / 13 : ℝ) / 3) = F (9 / 13) / 2 := h1 (9 / 13) (by constructor <;> norm_num)
      have h19b : (9 / 13 : ℝ) / 3 = (3 / 13 : ℝ) := by
        norm_num
      rw [h19b] at h19a
      linarith
    have h20 : F (4 / 13) = 1 - F (9 / 13) := by
      have h20a : F (1 - (9 / 13 : ℝ)) = 1 - F (9 / 13) := h2 (9 / 13) (by constructor <;> norm_num)
      have h20b : (1 - (9 / 13 : ℝ)) = (4 / 13 : ℝ) := by
        norm_num
      rw [h20b] at h20a
      linarith
    have h21 : F (4 / 13) = F (12 / 13) / 2 := by
      have h21a : F ((12 / 13 : ℝ) / 3) = F (12 / 13) / 2 := h1 (12 / 13) (by constructor <;> norm_num)
      have h21b : (12 / 13 : ℝ) / 3 = (4 / 13 : ℝ) := by
        norm_num
      rw [h21b] at h21a
      linarith
    have h22 : F (1 / 13) = 1 - F (12 / 13) := by
      have h22a : F (1 - (12 / 13 : ℝ)) = 1 - F (12 / 13) := h2 (12 / 13) (by constructor <;> norm_num)
      have h22b : (1 - (12 / 13 : ℝ)) = (1 / 13 : ℝ) := by
        norm_num
      rw [h22b] at h22a
      linarith
    linarith

  constructor
  · exact h10
  · exact h17