import Mathlib

theorem algebra_172294 {a : ℝ} (ha : a ≠ 0) (h : ∃ k : ℤ, a + 1 / a = k) (n : ℕ) :
    2 ≤ n ∧ n ≤ 7 → ∃ m : ℤ, a ^ n + 1 / a ^ n = m := by
  intro h1
  rcases h with ⟨k, hk⟩
  have h2 : 2 ≤ n := h1.1
  have h3 : n ≤ 7 := h1.2
  have h4 : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases h4 with (rfl | rfl | rfl | rfl | rfl | rfl)
  · -- n = 2
    use k^2 - 2
    have h2 : a ^ 2 + 1 / a ^ 2 = (k : ℝ) ^ 2 - 2 := by
      have h5 : a ^ 2 + 1 / a ^ 2 = (a + 1 / a) ^ 2 - 2 := by
        field_simp
        ring
      rw [h5, hk]
    norm_num at h2 ⊢
    all_goals linarith
  · -- n = 3
    use k^3 - 3 * k
    have h3 : a ^ 3 + 1 / a ^ 3 = (k : ℝ) ^ 3 - 3 * (k : ℝ) := by
      have h6 : a ^ 3 + 1 / a ^ 3 = (a + 1 / a) ^ 3 - 3 * (a + 1 / a) := by
        field_simp
        ring
      rw [h6, hk]
    norm_num at h3 ⊢
    all_goals linarith
  · -- n = 4
    use k^4 - 4 * k^2 + 2
    have h4 : a ^ 4 + 1 / a ^ 4 = (k : ℝ) ^ 4 - 4 * (k : ℝ) ^ 2 + 2 := by
      have h7 : a ^ 4 + 1 / a ^ 4 = (a + 1 / a) ^ 4 - 4 * (a + 1 / a) ^ 2 + 2 := by
        field_simp
        ring
      rw [h7, hk]
    norm_num at h4 ⊢
    all_goals linarith
  · -- n = 5
    use k^5 - 5 * k^3 + 5 * k
    have h5 : a ^ 5 + 1 / a ^ 5 = (k : ℝ) ^ 5 - 5 * (k : ℝ) ^ 3 + 5 * (k : ℝ) := by
      have h8 : a ^ 5 + 1 / a ^ 5 = (a + 1 / a) ^ 5 - 5 * (a + 1 / a) ^ 3 + 5 * (a + 1 / a) := by
        field_simp
        ring
      rw [h8, hk]
    norm_num at h5 ⊢
    all_goals linarith
  · -- n = 6
    use k^6 - 6 * k^4 + 9 * k^2 - 2
    have h6 : a ^ 6 + 1 / a ^ 6 = (k : ℝ) ^ 6 - 6 * (k : ℝ) ^ 4 + 9 * (k : ℝ) ^ 2 - 2 := by
      have h9 : a ^ 6 + 1 / a ^ 6 = (a + 1 / a) ^ 6 - 6 * (a + 1 / a) ^ 4 + 9 * (a + 1 / a) ^ 2 - 2 := by
        field_simp
        ring
      rw [h9, hk]
    norm_num at h6 ⊢
    all_goals linarith
  · -- n = 7
    use k^7 - 7 * k^5 + 14 * k^3 - 7 * k
    have h7 : a ^ 7 + 1 / a ^ 7 = (k : ℝ) ^ 7 - 7 * (k : ℝ) ^ 5 + 14 * (k : ℝ) ^ 3 - 7 * (k : ℝ) := by
      have h10 : a ^ 7 + 1 / a ^ 7 = (a + 1 / a) ^ 7 - 7 * (a + 1 / a) ^ 5 + 14 * (a + 1 / a) ^ 3 - 7 * (a + 1 / a) := by
        field_simp
        ring
      rw [h10, hk]
    norm_num at h7 ⊢
    all_goals linarith