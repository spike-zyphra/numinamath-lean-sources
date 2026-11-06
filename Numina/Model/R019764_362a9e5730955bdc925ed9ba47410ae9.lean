import Mathlib

theorem algebra_215111 {a : ℝ} (ha : a ≠ 0) (h : a / 2 + 2 / a = 3) :
    (a ^ 8 + 256) / (16 * a ^ 4) = 47 := by
  have h1 : a ^ 2 + 4 = 6 * a := by
    have h2 : a / 2 + 2 / a = 3 := h
    have h3 : a * (a / 2 + 2 / a) = a * 3 := by
      rw [h2]
    have h4 : a * (a / 2 + 2 / a) = a^2 / 2 + 2 := by
      field_simp [ha]
      <;> ring
    have h5 : a * 3 = 3 * a := by ring
    rw [h4, h5] at h3
    linarith
  
  have h2 : a ^ 4 = 168 * a - 128 := by
    have h3 : a ^ 2 = 6 * a - 4 := by linarith
    calc
      a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ = (6 * a - 4) ^ 2 := by rw [h3]
      _ = 36 * a ^ 2 - 48 * a + 16 := by ring
      _ = 36 * (6 * a - 4) - 48 * a + 16 := by rw [show a ^ 2 = 6 * a - 4 by linarith]
      _ = 168 * a - 128 := by linarith
  
  have h3 : a ^ 8 + 256 = 47 * (16 * a ^ 4) := by
    have h5 : a^4 = 168 * a - 128 := h2
    calc
      a ^ 8 + 256 = (a^4) ^ 2 + 256 := by ring
      _ = (168 * a - 128) ^ 2 + 256 := by rw [h5]
      _ = 28224 * a^2 - 43008 * a + 16384 + 256 := by ring
      _ = 28224 * (6 * a - 4) - 43008 * a + 16384 + 256 := by rw [show a ^ 2 = 6 * a - 4 by linarith]
      _ = 752 * (168 * a - 128) := by nlinarith
      _ = 47 * (16 * a^4) := by
        rw [show a^4 = 168 * a - 128 by linarith [h2]]
        all_goals ring
  
  have h4 : a^4 ≠ 0 := by
    by_contra h5
    have h6 : a^4 = 0 := by linarith
    have h7 : a = 0 := by
      have h8 : a^4 = 0 := h6
      have : a^4 = 0 := h8
      have h9 : a^2 = 0 := by 
        nlinarith [sq_nonneg (a^2), sq_nonneg (a)]
      have h10 : a = 0 := by
        nlinarith [sq_pos_of_ne_zero (show (a) ≠ 0 by assumption), sq_nonneg (a)]
      exact h10
    contradiction
  
  rw [show a ^ 8 + 256 = 47 * (16 * a ^ 4) by linarith [h3]]
  have h7 : (47 * (16 * a ^ 4) ) / (16 * a ^ 4) = 47 := by
    have h8 : a ^ 4 ≠ 0 := h4
    field_simp [h8]
    <;> nlinarith
  
  exact h7