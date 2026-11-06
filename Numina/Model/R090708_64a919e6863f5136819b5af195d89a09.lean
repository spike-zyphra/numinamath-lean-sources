import Mathlib

theorem algebra_599005 (f : ℝ → ℝ) (p : ℝ) (hp : 0 < p ∧ p < 15)
    (h : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
    IsLeast {y | ∃ x, x ∈ Set.Icc p 15 ∧ f x = y} 15 := by
  constructor
  · -- First part: Show 15 is achievable, by some x
    use 15
    constructor
    · -- Show 15 ∈ [p, 15]
      have hp1 : p > 0 := hp.1
      have hp2 : p < 15 := hp.2
      exact ⟨by linarith, by norm_num⟩
    · -- Show f(15) = 15
      have h15 := h 15
      rw [h15]
      have hp1 : p > 0 := hp.1
      have hp2 : p < 15 := hp.2
      have h1 : abs (15 - p) = 15 - p := by
        rw [abs_of_pos]
        linarith
      have h2 : abs (15 - 15 : ℝ) = (0 : ℝ) := by
        norm_num
      have h3 : abs ((15 : ℝ) - p - 15) = p := by
        have hp1 : p > 0 := hp.1
        have h4 : (15 : ℝ) - p - 15 = -p := by ring
        rw [h4]
        rw [abs_of_neg (by linarith)]
        linarith
      rw [h1, h2, h3]
      all_goals linarith
  · -- Second part: Show 15 is the least element in the set
    rintro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx1 : p ≤ x := hx.left
    have hx2 : x ≤ 15 := hx.right
    have hfx2 : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15) := by
      apply h x
    rw [hfx2] at hfx
    have h1 : abs (x - p) = x - p := by
      rw [abs_of_nonneg]
      linarith
    have h2 : abs (x - 15) = 15 - x := by
      rw [abs_of_nonpos]
      linarith
      all_goals linarith
    have h3 : abs (x - p - 15) = p + 15 - x := by
      have hp1 : p > 0 := hp.1
      have h4 : (x - p - 15 : ℝ) < 0 := by
        nlinarith
      rw [abs_of_neg h4]
      nlinarith
    rw [h1, h2, h3] at hfx
    nlinarith