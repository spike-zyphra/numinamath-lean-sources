import Mathlib

theorem algebra_273206 (n : ℝ) (h : 0 < n) : (1 / (2 * n)) + (1 / (4 * n)) = 3 / 12 ↔ n = 3 := by
  constructor
  · -- Assume left side, prove right side
    intro h_eq
    have h1 : 1 / (2 * n) + 1 / (4 * n) = 3 / (4 * n) := by
      field_simp
      <;> ring
    have h2 : 3 / (4 * n) = 3 / 12 := by 
      rw [← h1]
      linarith [h_eq]
    have h3 : 4 * n ≠ 0 := by 
      nlinarith [h]
    have h4 : 3 * (12 : ℝ) = 3 * (4 * n) := by 
      field_simp [h3] at h2 ⊢
      linarith 
    have h5 : 36 = 12 * n := by 
      linarith 
    have hn : n = 3 := by 
      linarith 
    exact hn 
  · -- Assume right side, prove left side 
    intro h_eq
    rw [h_eq]
    norm_num
    <;> ring_nf <;> norm_num