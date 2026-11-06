import Mathlib

open Real

theorem algebra_21934:
  IsLeast {u:ℝ | ∃(a b:ℝ), u = a + 1/(b*(a-b)) ∧ 0 < a ∧ 0 < b ∧ b < a} 3 := by
  constructor
  · -- Show 3 is in the set
    use 2, 1
    norm_num
  · -- Show that 3 is the least
    intro u hu
    rcases hu with ⟨a, b, heq, ha, hb, h1⟩
    have h2 : 0 < a - b := by linarith
    have h3 : a + 1 / (b * (a - b)) - 3 ≥ 0 := by
      have h4 : 0 < b * (a - b) := by
        apply mul_pos
        linarith
        linarith
      have h5 : a + 1 / (b * (a - b)) - 3 = ((a - 3) * (b * (a - b)) + 1) / (b * (a - b)) := by
        field_simp
        <;> ring
      have h6 : ((a - 3) * (b * (a - b)) + 1) ≥ 0 := by
        nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 1), sq_nonneg ((a - b) - 1), 
                  sq_nonneg (b * (a - b - 1)), sq_nonneg (a * (b - 1)), 
                  mul_pos ha hb, mul_pos hb (show 0 < a - b by linarith), 
                  mul_pos (show 0 < a - b by linarith) ha]
      have h7 : (b * (a - b) : ℝ) > (0 : ℝ) := by
        apply mul_pos
        linarith
        linarith
      rw [h5]
      apply div_nonneg
      linarith
      linarith
    linarith [heq, h3]