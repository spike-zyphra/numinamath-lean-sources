import Mathlib

theorem algebra_212618 (a : ℝ) (ha : 0 < a) (h : a < 15) :
    IsLeast {x | ∃ t, x = abs (t - a) + abs (t - 15) + abs (t - a - 15) ∧ a ≤ t ∧ t ≤ 15} 15 := by
  constructor
  · -- Show 15 is in the set.
    use 15
    constructor
    · -- Show equality of expression.
      have h1 : a < 15 := by linarith
      have h2 : (15 : ℝ) - a > 0 := by linarith
      have h3 : (15 : ℝ) - 15 = (0 : ℝ) := by norm_num
      have h4 : (15 : ℝ) - a - 15 = -a := by linarith
      have h5 : abs ((15 : ℝ) - a) = (15 - a : ℝ) := by
        rw [show (15 : ℝ) - a = (15 - a) by linarith]
        apply abs_of_nonneg
        linarith
      have h6 : abs ((15 : ℝ) - 15) = (0 : ℝ) := by
        rw [show (15 : ℝ) - 15 = (0 : ℝ) by linarith]
        norm_num
      have h7 : abs ((15 : ℝ) - a - 15) = abs (-a : ℝ) := by
        have h8 : (15 : ℝ) - a - 15 = -a := by linarith
        rw [h8]
      have h8 : abs (-a : ℝ) = abs (a : ℝ) := by
        rw [show (-a : ℝ) = -a by linarith]
        rw [abs_neg]
      have h9 : abs (a : ℝ) = a := by
        rw [abs_of_pos ha]
      have h10 : abs ((15 : ℝ) - a - 15) = a := by
        rw [h7, h8, h9]
      linarith [h5, h6, h10]
    constructor
    · -- Show a ≤ 15
      linarith
    · -- Show 15 ≤ 15
      norm_num
  · -- Show 15 is minimal.
    intro x hx
    rcases hx with ⟨t, heq, ht1, ht2⟩
    have h1 : a ≤ t := ht1
    have h2 : t ≤ 15 := ht2
    have h3 : t - a ≥ 0 := by linarith
    have h4 : t - 15 ≤ 0 := by linarith
    have h5 : t - a - 15 < 0 := by
      nlinarith
    have h6 : abs (t - a) = t - a := by
      rw [abs_of_nonneg (show t - a ≥ 0 by linarith)]
    have h7 : abs (t - 15) = 15 - t := by
      have h8 : t - 15 ≤ 0 := by linarith
      rw [abs_of_nonpos (show t - 15 ≤ 0 by linarith)]
      all_goals linarith
    have h8 : abs (t - a - 15) = a + 15 - t := by
      have h9 : (t - a - 15 : ℝ) < 0 := by
        nlinarith
      rw [abs_of_neg h9]
      all_goals linarith
    have h11 : abs (t - a) + abs (t - 15) + abs (t - a - 15) ≥ 15 := by
      rw [h6, h7, h8]
      nlinarith
    linarith [heq, h11]