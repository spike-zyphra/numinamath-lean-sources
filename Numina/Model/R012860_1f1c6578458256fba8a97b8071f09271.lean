import Mathlib

theorem algebra_7930 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : 9 * x + 9 * y - 2 * x * y + 19 = 0) :
    (x = 5 ∧ y = 64) ∨ (x = 8 ∧ y = 13) ∨ (x = 13 ∧ y = 8) ∨ (x = 64 ∧ y = 5) := by
  have h1 : x ≥ 1 := by linarith
  have h2 : y ≥ 1 := by linarith
  have h3 : 2 * x - 9 ∣ 119 := by
    have eq1 : 18 * x + 38 = 2 * y * (2 * x - 9) := by
      nlinarith [h]
    have eq2 : (2 * x - 9) ∣ (18 * x + 38) := by
      use 2 * y
      linarith
    have eq3 : (2 * x - 9) ∣ 119 := by
      have h4 : (2 * x - 9) ∣ (18 * x + 38) := eq2
      have h5 : (2 * x - 9) ∣ (2 * x - 9) * 9 := by
        apply dvd_mul_of_dvd_left
        exact dvd_refl (2 * x - 9)
      have h6 : (2 * x - 9) ∣ (18 * x + 38 - (2 * x - 9) * 9) := by
        apply Int.dvd_sub
        · exact h4
        · exact h5
      have h7 : (18 * x + 38 - (2 * x - 9) * 9) = 119 := by
        nlinarith
      rw [h7] at h6
      exact h6
    exact eq3
  have h4 : 2 * x - 9 > 0 := by
    by_contra h4
    push_neg at h4
    have h5 : x ≤ 4 := by
      omega
    interval_cases x <;> omega
  have h6 : 2 * x - 9 > 0 := h4
  have h8 : (2 * x - 9) = 1 ∨ (2 * x - 9) = 7 ∨ (2 * x - 9) = 17 ∨ (2 * x - 9) = 119 := by
    have h9 : (2 * x - 9) ∣ 119 := h3
    have h10 : (2 * x - 9) > 0 := h6
    have h11 : (2 * x - 9) ≤ 119 := by
      exact Int.le_of_dvd (by norm_num) h9
    interval_cases (2 * x - 9) <;> try { tauto }
  rcases h8 with h8 | h8 | h8 | h8
  · -- Case where 2x - 9 = 1, so x = 5, y = 64
    have hx1 : 2 * x - 9 = 1 := h8
    have hx2 : x = 5 := by
      omega
    have hy1 : y = 64 := by
      nlinarith [h, hx2]
    left
    exact ⟨hx2, hy1⟩
  · -- Case where 2x - 9 = 7, so x = 8, y = 13
    have hx1 : 2 * x - 9 = 7 := h8
    have hx2 : x = 8 := by
      omega
    have hy1 : y = 13 := by
      nlinarith [h, hx2]
    right
    left
    exact ⟨hx2, hy1⟩
  · -- Case where 2x - 9 = 17, so x = 13, y = 8
    have hx1 : 2 * x - 9 = 17 := h8
    have hx2 : x = 13 := by
      omega
    have hy1 : y = 8 := by
      nlinarith [h, hx2]
    right
    right
    left
    exact ⟨hx2, hy1⟩
  · -- Case where 2x - 9 = 119, so x = 64, y = 5
    have hx1 : 2 * x - 9 = 119 := h8
    have hx2 : x = 64 := by
      omega
    have hy1 : y = 5 := by
      nlinarith [h, hx2]
    right
    right
    right
    exact ⟨hx2, hy1⟩