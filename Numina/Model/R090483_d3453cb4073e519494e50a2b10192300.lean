import Mathlib

theorem algebra_318198 (f : ℝ → ℝ) (hf : f = fun x => -x - 9 / x + 18) :
    IsGreatest (Set.image f {x | 0 < x}) 12 := by 
  constructor
  · -- Show that 12 is attained by proving there exists some x in {x | 0 < x} such that f x = 12
    use 3
    constructor
    · -- Show that 3 is in the domain
      norm_num 
    · -- Show that f 3 = 12
      rw [hf]
      norm_num
  · -- Show that for all y in the image, y ≤ 12
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx_pos : 0 < x := by simpa using hx
    rw [hf] at hfx
    have h1 : y = -x - 9 / x + 18 := by 
      simp at hfx ⊢
      linarith 
    have h2 : x + 9 / x ≥ 6 := by 
      have h3 : x * (9 / x) = 9 := by 
        field_simp
        all_goals linarith 
      nlinarith [sq_nonneg (x - 3)]
    linarith [h1, h2]