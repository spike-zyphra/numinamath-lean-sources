import Mathlib

theorem algebra_307350 (a : ℕ → ℝ) (ha : ∀ n ∈ Finset.range 5, 0 < a n)
    (h1 : ∃ d, a 0 + d = a 1 ∧ a 1 + d = a 2)
    (h2 : ∃ r, a 1 * r = a 2 ∧ a 2 * r = a 3)
    (h3 : r ≠ 1)
    (h4 : ∃ d, 1 / a 2 + d = 1 / a 3 ∧ 1 / a 3 + d = 1 / a 4) :
    ∃ r, a 0 * r = a 2 ∧ a 2 * r = a 4 := by
  rcases h1 with ⟨d, h11, h12⟩
  rcases h2 with ⟨r, h21, h22⟩
  rcases h4 with ⟨d', h41, h42⟩
  have h5 : 0 < a 0 := ha 0 (by simp)
  have h6 : 0 < a 1 := ha 1 (by simp)
  have h7 : 0 < a 2 := ha 2 (by simp)
  have h8 : 0 < a 3 := ha 3 (by simp)
  have h9 : 0 < a 4 := ha 4 (by simp)
  use a 2 / a 0
  constructor
  · -- Show that a 0 * (a 2 / a 0) = a 2
    field_simp [show 0 < a 0 by linarith, show a 0 ≠ 0 by linarith]
    all_goals nlinarith
  · -- Show that a 2 * (a 2 / a 0) = a 4
    field_simp [show 0 < a 0 by linarith, show a 0 ≠ 0 by linarith, show 0 < a 2 by linarith, show a 2 ≠ 0 by linarith]
    all_goals
      ring_nf at h11 h12 h21 h22 h41 h42 ⊢
      field_simp [show 0 < a 2 by linarith, show a 2 ≠ 0 by linarith, show 0 < a 3 by linarith, show a 3 ≠ 0 by linarith, show 0 < a 4 by linarith, show a 4 ≠ 0 by linarith] at h41 h42 ⊢
      <;> nlinarith [h11, h12, h21, h22, h41, h42, mul_pos h5 h6, mul_pos h5 h7, mul_pos h5 h8, mul_pos h5 h9, mul_pos h6 h7, mul_pos h6 h8, mul_pos h6 h9, mul_pos h7 h8, mul_pos h7 h9, mul_pos h8 h9, sq_pos_of_pos h5, sq_pos_of_pos h6, sq_pos_of_pos h7, sq_pos_of_pos h8, sq_pos_of_pos h9]