import Mathlib

theorem algebra_10646 (f : ℝ → ℝ) (hf : f = fun x => 3 * x ^ 2 + 6 * x + 9) :
    IsLeast (Set.image f (Set.univ : Set ℝ)) 6 := by 
  constructor
  · -- Show that 6 is in the image.
    use -1
    simp [hf]
    all_goals norm_num 
  · -- Show that 6 is a lower bound 
    intro y
    rintro ⟨x, hx⟩
    simp [hf] at hx
    have h : 3 * (x + 1) ^ 2 + 6 ≥ 6 := by
      nlinarith [sq_nonneg (x + 1)]
    have : 3 * x ^ 2 + 6 * x + 9 = 3 * (x + 1) ^ 2 + 6 := by ring
    linarith