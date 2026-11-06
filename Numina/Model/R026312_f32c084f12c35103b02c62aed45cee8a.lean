import Mathlib

open BigOperators Real Set

theorem inequalities_1301 {m : ℝ} (h : ∀ x, (-x + 4 * m < x + 10 ∧ x + 1 > m) ↔ x > 4) :
    m = 9 / 2 := by
  have h1 : m ≥ 4.5 := by
    by_contra h1
    push_neg at h1
    have h2 : m < 4.5 := by linarith
    have h3 : (- (4 : ℝ) + 4 * m < (4 : ℝ) + 10 ∧ (4 : ℝ) + 1 > m) := by
      constructor
      ·
        nlinarith
      ·
        nlinarith
    have h4 : ((- (4 : ℝ) + 4 * m < (4 : ℝ) + 10 ∧ (4 : ℝ) + 1 > m) ) ↔ (4 : ℝ) > 4 := by
      apply h 4
    have h5 : ((- (4 : ℝ) + 4 * m < (4 : ℝ) + 10 ∧ (4 : ℝ) + 1 > m) ) := by
      tauto
    have h7 : (4 : ℝ) > (4 : ℝ) := by
      tauto
    linarith
  have h8 : m ≤ 4.5 := by
    by_contra h2
    push_neg at h2
    have h20 : m > (4.5 : ℝ) := by linarith
    have h9 : (2 * m - 5 : ℝ) > (4 : ℝ) := by
      nlinarith
    have h10 : (- (2 * m - 5 : ℝ) + 4 * m < (2 * m - 5 : ℝ) + 10 ∧ (2 * m - 5 : ℝ) + 1 > m) ↔ (2 * m - 5 : ℝ) > 4 := by
      apply h (2 * m - 5)
    have h12 : ((2 * m - 5 : ℝ) > (4 : ℝ)) := by linarith
    have h14 : ¬ ((- (2 * m - 5 : ℝ) + 4 * m < (2 * m - 5 : ℝ) + 10 ∧ (2 * m - 5 : ℝ) + 1 > m) ) := by
      intro h14
      have h15 : (- (2 * m - 5 : ℝ) + 4 * m < (2 * m - 5 : ℝ) + 10) := by
        tauto
      have h16 : ((2 * m - 5 : ℝ) + 1 > m) := by
        tauto
      nlinarith
    have h13 : ((- (2 * m - 5 : ℝ) + 4 * m < (2 * m - 5 : ℝ) + 10 ∧ (2 * m - 5 : ℝ) + 1 > m) ) := by
      have h10 : ((- (2 * m - 5 : ℝ) + 4 * m < (2 * m - 5 : ℝ) + 10 ∧ (2 * m - 5 : ℝ) + 1 > m) ) ↔ (2 * m - 5 : ℝ) > 4 := by
        apply h (2 * m - 5)
      tauto
    exfalso
    tauto
  have h17 : m = (4.5 : ℝ) := by
    linarith
  rw [h17]
  norm_num