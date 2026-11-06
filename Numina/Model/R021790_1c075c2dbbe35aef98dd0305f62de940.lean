import Mathlib

theorem algebra_104680 (p : ℝ) (hp : 0 < p ∧ p < 15) (f : ℝ → ℝ)
    (hf : ∀ x, f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) :
    IsLeast {y | ∃ x, x ∈ Set.Icc p 15 ∧ f x = y} 15 := by
  constructor
  · -- Show 15 is in the set
    use 15
    constructor
    · -- Show 15 ∈ [p, 15]
      have hp1 : p ≤ 15 := by linarith [hp.right]
      exact ⟨by linarith, by linarith⟩
    · -- Calculate f(15)
      rw [hf 15]
      have hp1 : 0 < p := hp.1
      have hp2 : p < 15 := hp.2
      have h1 : abs (15 - p) = 15 - p := by
        rw [abs_of_pos]
        linarith
      have h2 : abs ((15 : ℝ) - (15 : ℝ)) = 0 := by
        norm_num [abs_zero]
      have h3 : abs (15 - p - 15) = p := by
        have h5 : (15 - p - 15 : ℝ) = -p := by linarith
        rw [h5]
        rw [abs_of_neg (by linarith)]
        all_goals linarith
      rw [h1, h2, h3]
      all_goals linarith
  · -- Show no value less than 15 is in the set
    rintro y ⟨x, hx, hfx⟩
    rcases hx with ⟨hx1, hx2⟩
    have hfx_eq : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15) := hf x
    rw [hfx_eq] at hfx
    have h1 : abs (x - p) = x - p := by
      rw [abs_of_nonneg]
      linarith
    have h2 : abs (x - 15) = 15 - x := by
      rw [abs_of_nonpos]
      linarith
      all_goals linarith
    have h3 : abs (x - p - 15) = (p + 15) - x := by
      have h5 : x - p - 15 ≤ 0 := by 
        nlinarith
      rw [abs_of_nonpos h5]
      all_goals linarith
    rw [h1, h2, h3] at hfx
    linarith