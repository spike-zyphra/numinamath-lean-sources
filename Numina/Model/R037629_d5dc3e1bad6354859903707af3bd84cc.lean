import Mathlib

  theorem algebra_259254 :
  IsGreatest {z : ℝ | ∃ x y : ℝ , x + y = 5 ∧ z = x^2 + 2 * x * y} 25 := by
  constructor
  · -- Show 25 is in the set
    use 5, 0
    constructor
    · norm_num
    · norm_num
  · -- Show no element greater than 25 is in the set
    intro z h
    rcases h with ⟨x, y, h1, h2⟩
    have eq1 : y = 5 - x := by linarith
    have eq2 : x^2 + 2 * x * y = -x^2 + 10 * x := by
      rw [eq1]
      nlinarith 
    nlinarith [sq_nonneg (x - 5), h2, eq2]