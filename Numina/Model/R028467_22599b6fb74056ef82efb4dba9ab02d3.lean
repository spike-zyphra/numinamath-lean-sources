import Mathlib
theorem algebra_610513 : IsGreatest {S : ℝ | ∃ a b c : ℝ, ∃ P : ℝ → ℝ, (P = fun x => a * x ^ 2 + b * x + c) ∧ P 1 = 20 ∧ P (-1) = 22 ∧ P (P 0) = 400 ∧ S = P 10} 2486:= by
  constructor
  · -- Show 2486 is in the set
    use 25, -1, -4
    use (fun x => 25 * x ^ 2 + -1 * x + -4)
    constructor
    · -- Show P = fun x => 25 * x^2 + -1 * x + -4
      rfl
    constructor
    · -- Show P 1 = 20
      norm_num
    constructor
    · -- Show P (-1) = 22
      norm_num
    constructor
    · -- Show P (P 0) = 400
      norm_num
    · -- Show 2486 = P 10
      norm_num
  · -- Show that 2486 is the greatest in the set
    intro S h
    rcases h with ⟨a, b, c, P, hP_def, hP1, hP_n1, hP_P0, hS_eq⟩
    simp [hP_def] at hP1 hP_n1 hP_P0 hS_eq
    nlinarith [sq_nonneg (a - 25), sq_nonneg (c + 4), sq_nonneg (c - 21 + a), sq_nonneg (b + 1), sq_nonneg (a * c - 25 * (-4)), sq_nonneg ((a - 25) * (c + 4))]