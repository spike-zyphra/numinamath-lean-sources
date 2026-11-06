import Mathlib

theorem algebra_20309 (f : ℝ → ℝ) (hf : f = fun x => 4 * (x + 7) * (2 - x)) :
    IsGreatest (Set.image f (Set.univ : Set ℝ)) 81 := by
  constructor
  · -- Show 81 is in the image of f over ℝ
    use -5 / 2
    norm_num [hf]
  · -- Show 81 is indeed the greatest
    intro y
    rintro ⟨x, hx⟩
    simp [hf] at hx
    have h1 : 4 * (x + 7) * (2 - x) ≤ 81 := by
      nlinarith [sq_nonneg (x + 5 / 2)]
    linarith [h1]