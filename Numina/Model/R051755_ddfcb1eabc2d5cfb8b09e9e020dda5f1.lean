import Mathlib

theorem algebra_312566 (a : ℝ) (ha : 0 < a ∧ a < 15) :
    IsLeast {y | ∃ x, a ≤ x ∧ x ≤ 15 ∧ y = abs (x - a) + abs (x - 15) + abs (x - a - 15)} 15 := by
  constructor
  · -- Show 15 is in the set
    use 15
    constructor
    · -- Show that a ≤ 15
      linarith [ha.right]
    constructor
    · -- Show that 15 ≤ 15
      all_goals linarith
    · -- Show that 15 = |15 - a| + |15 - 15| + |15 - a - 15|
      have ha1 : 0 < a := ha.left
      have ha2 : a < 15 := ha.right
      have h1 : abs (15 - a) = 15 - a := by
        rw [abs_of_pos]
        linarith
      have h2 : abs (15 - 15 : ℝ) = 0 := by
        norm_num
      have h3 : abs ((15 : ℝ) - a - (15 : ℝ)) = abs (-a) := by
        ring_nf
      have h4 : abs (-a) = a := by
        rw [abs_neg]
        rw [abs_of_pos]
        linarith
      rw [h1, h2, h3, h4]
      all_goals linarith
  · -- Show 15 is the least
    intro y hy
    rcases hy with ⟨x, hx1, hx2, heq⟩
    have h1 : abs (x - a) = x - a := by
      rw [abs_of_nonneg]
      linarith
    have h2 : abs (x - 15) = 15 - x := by
      rw [abs_of_nonpos]
      linarith
      all_goals linarith
    have h3' : abs (x - a - 15) = - (x - a - 15) := by
      rw [abs_of_nonpos]
      nlinarith
      all_goals linarith
    rw [heq]
    rw [h1, h2, h3']
    all_goals nlinarith