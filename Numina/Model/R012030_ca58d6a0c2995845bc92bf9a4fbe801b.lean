import Mathlib

theorem algebra_3149  : 
  {x : ℝ | 0 < x ∧ 3*x^2-20*x=7} = {7} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x in {x : ℝ | 0 < x ∧ 3*x^2-20*x=7}, prove x = 7
    rintro ⟨hx, heq⟩
    have h1 : 3 * x ^ 2 - 20 * x - 7 = 0 := by linarith
    have h2 : (3 * x + 1) * (x - 7) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- case where 3x + 1 = 0 
      have h5 : x = -1 / 3 := by linarith
      linarith -- contradiction with 0 < x
    · -- case where x - 7 = 0 
      linarith -- x = 7 
  · -- Assume x = 7, prove 0 < x ∧ 3*x^2-20*x=7 
    intro heq 
    rw [heq]
    constructor <;> norm_num