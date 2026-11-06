import Mathlib

theorem algebra_10151 :
  IsLeast {x : ℝ | ∃ a b : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ a + b = 9 ∧ x = max (max (a ^ 2) (4 * b ^ 2)) (2 * a * b)} 36 := by
  constructor
  · -- Show that 36 is in the set.
    use 6, 3
    norm_num [max_assoc, max_comm, max_left_comm]
  · -- Show that for any x in the set, 36 ≤ x.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hsum, hx⟩
    by_contra h
    push_neg at h
    have h1 : max (max (a ^ 2) (4 * b ^ 2)) (2 * a * b) < 36 := by linarith [h, hx]
    have h2 : a ^ 2 < 36 := by
      have h3 : max (max (a ^ 2) (4 * b ^ 2)) (2 * a * b) ≥ a ^ 2 := by
        simp [max_le_iff]
      linarith [h1, h3]
    have h3 : 4 * b ^ 2 < 36 := by
      have h4 : max (max (a ^ 2) (4 * b ^ 2)) (2 * a * b) ≥ 4 * b ^ 2 := by
        simp [max_le_iff]
      linarith [h1, h4]
    have h4 : 2 * a * b < 36 := by
      have h5 : max (max (a ^ 2) (4 * b ^ 2)) (2 * a * b) ≥ 2 * a * b := by
        simp [max_le_iff]
      linarith [h1, h5]
    have h5 : a < 6 := by
      nlinarith
    have h6 : b > 3 := by
      nlinarith [h5, hsum]
    have h7 : b < 3 := by
      nlinarith [h3]
    linarith [h6, h7]