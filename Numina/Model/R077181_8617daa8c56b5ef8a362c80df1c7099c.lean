import Mathlib

theorem algebra_105989 (p : ℝ) (hp : 0 < p ∧ p < 15) (f : ℝ → ℝ)
    (hf : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
    IsLeast {y | ∃ x, p ≤ x ∧ x ≤ 15 ∧ f x = y} 15 := by
  constructor
  · -- Show 15 is achievable, so exists x in [p, 15] such that f x = 15
    use 15
    constructor
    · -- Show p ≤ 15
      linarith [hp.1, hp.2]
    constructor
    · -- Show 15 ≤ 15
      linarith
    · -- Show f 15 = 15
      rw [hf 15]
      have hp1 : p > 0 := hp.1
      have hp2 : p < 15 := hp.2
      have h1 : abs (15 - p) = 15 - p := by
        rw [abs_of_pos]
        linarith
        all_goals linarith
      have h2 : abs (15 - 15 : ℝ) = (0 : ℝ) := by
        norm_num
      have h3 : abs (15 - p - 15 : ℝ) = abs ( -(p : ℝ) ) := by
        have h5 : (15 - p - 15 : ℝ) = -p := by ring
        rw [h5]
      have h7 : abs (15 - p : ℝ) = (15 - p : ℝ) := h1
      have h8 : abs (15 - 15 : ℝ) = (0 : ℝ) := h2
      have h9 : abs (15 - p - 15 : ℝ) = (p : ℝ) := by
        rw [h3]
        have h6 : abs (-(p : ℝ)) = (p : ℝ) := by
          have hp7 : p > 0 := hp.1
          have : abs (-(p : ℝ)) = abs (p : ℝ) := by
            rw [abs_neg]
          rw [this]
          rw [abs_of_pos hp7]
        rw [h6]
      rw [h7, h8, h9]
      all_goals linarith
  · -- Show that 15 is the smallest
    intro y hy
    rcases hy with ⟨x, hx1, hx2, hfx⟩
    have h1 : abs (x - p) = x - p := by
      rw [abs_of_nonneg]
      linarith
    have h2 : abs (x - 15 : ℝ) = 15 - x := by
      have h3 : (x - 15 : ℝ) ≤ 0 := by linarith
      rw [abs_of_nonpos h3]
      all_goals linarith
    have h4 : abs (x - p - 15) = - (x - p - 15 : ℝ) := by
      have h5 : (x - p - 15 : ℝ) ≤ 0 := by
        linarith [show x ≤ 15 by linarith]
      rw [abs_of_nonpos h5]
      all_goals linarith
    have eq1 : f x = 30 - x := by
      rw [hf x]
      rw [h1, h2, h4]
      linarith
    have eq2 : y = 30 - x := by
      linarith [eq1, hfx]
    linarith [eq2, hx2]