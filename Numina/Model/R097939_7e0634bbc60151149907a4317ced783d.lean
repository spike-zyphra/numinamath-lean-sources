import Mathlib

theorem algebra_128543 (f : ℝ → ℝ) (hf : f = fun x => -x - 9 / x + 18) :
    IsGreatest {y | ∃ x, x > 0 ∧ f x = y} 12 := by 
  constructor 
  · -- Show 12 is in the set 
    use 3 
    constructor 
    · norm_num 
    · -- Calculate value at 3 
      rw [hf]
      norm_num 
  · -- Show any value in the set is ≤ 12 
    intro y hy 
    rcases hy with ⟨x, hx, hfy⟩ 
    rw [hf] at hfy
    have h1 : -x - 9 / x + 18 = y := by 
      simpa using hfy 
    have h2 : x + 9 / x ≥ 6 := by 
      have h3 : x > 0 := hx 
      have h4 : x + 9 / x - 6 ≥ 0 := by 
        have h5 : x + 9 / x - 6 = (x^2 + 9 - 6 * x) / x := by 
          field_simp 
          ring 
        rw [h5] 
        -- Show numerator is ≥ 0 
        have h6 : x^2 + 9 - 6 * x ≥ 0 := by 
          have h7 : x^2 + 9 - 6 * x = (x - 3)^2 := by 
            ring 
          rw [h7] 
          apply sq_nonneg 
        have h8 : x > 0 := hx 
        apply div_nonneg 
        linarith 
        linarith 
      linarith 
    have h3 : -x - 9 / x + 18 ≤ 12 := by 
      have h4 : x + 9 / x ≥ 6 := h2 
      linarith 
    linarith [h1, h3] 
  all_goals try linarith 
  all_goals try tauto 
  all_goals try linarith 
  all_goals try tauto 
  all_goals try linarith 
  all_goals try tauto 
  all_goals try linarith 
  all_goals try tauto 
  all_goals try linarith 
  all_goals try tauto