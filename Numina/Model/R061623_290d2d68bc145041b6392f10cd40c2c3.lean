import Mathlib

open Matrix

theorem calculus_16432 :
    IsLeast {x | ∃ a b c d : ℤ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
      !![3, 0; 0, 2] * !![a, b; c, d] =
        !![a, b; c, d] * !![18, 12; -20, -13] ∧ x = a + b + c + d} 16 := by

  constructor
  · -- Show 16 is achievable
    use 4, 3, 5, 4
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
    <;> tauto
  · -- Show there's no smaller solution
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, heq, hx⟩
    have eq1 := congr_arg (fun M => M 0 0) heq
    have eq2 := congr_arg (fun M => M 0 1) heq
    have eq3 := congr_arg (fun M => M 1 0) heq
    have eq4 := congr_arg (fun M => M 1 1) heq
    simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at eq1 eq2 eq3 eq4
    omega