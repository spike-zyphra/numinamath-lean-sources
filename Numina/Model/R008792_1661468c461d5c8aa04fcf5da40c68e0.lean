import Mathlib

theorem algebra_10380 (f : ℝ → ℝ) (hf : f = fun r => -5 * r ^ 2 + 40 * r - 12) :
    IsGreatest {x | ∃ r, f r = x} 68 := by 
  constructor 
  · -- First prove that 68 belongs to the set.
    use 4 
    rw [hf]
    norm_num 
  · -- Now prove that 68 is indeed the greatest element.
    intro x hx 
    rcases hx with ⟨r, hr⟩
    rw [hf] at hr 
    simp at hr 
    have h : -5 * (r - 4) ^ 2 ≤ 0 := by 
      apply mul_nonpos_of_nonpos_of_nonneg 
      · norm_num 
      · apply pow_two_nonneg 
    nlinarith [sq_nonneg (r - 4)]