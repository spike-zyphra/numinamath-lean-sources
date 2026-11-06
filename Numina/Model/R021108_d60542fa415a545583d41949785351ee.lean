import Mathlib

theorem algebra_142294 :
    ∃ f g h : Polynomial ℝ, f.degree = 2 ∧ g.degree = 2 ∧ h.degree = 2 ∧
      (∃ x y : ℝ, f.eval x = 0 ∧ f.eval y = 0) ∧
      (∃ x y : ℝ, g.eval x = 0 ∧ g.eval y = 0) ∧
      (∃ x y : ℝ, h.eval x = 0 ∧ h.eval y = 0) ∧
      ¬∃ x : ℝ, (f + g).eval x = 0 ∧
      ¬∃ x : ℝ, (g + h).eval x = 0 ∧
      ¬∃ x : ℝ, (h + f).eval x = 0 := by
  use Polynomial.X^2 - 3 * Polynomial.X + 2
  use Polynomial.X^2 - 7 * Polynomial.X + 12
  use Polynomial.X^2 - 11 * Polynomial.X + 30
  constructor
  · -- Show f has degree 2
    compute_degree!
    all_goals norm_num
  constructor
  · -- Show g has degree 2
    compute_degree!
    all_goals norm_num
  constructor
  · -- Show h has degree 2
    compute_degree!
    all_goals norm_num
  constructor
  · -- Show f has two roots
    use 1, 2
    constructor
    · -- Show f.eval 1 = 0
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
      all_goals norm_num
    · -- Show f.eval 2 = 0
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
      all_goals norm_num
  constructor
  · -- Show g has two roots
    use 3, 4
    constructor
    · -- Show g.eval 3 = 0
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
      all_goals norm_num
    · -- Show g.eval 4 = 0
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
      all_goals norm_num
  constructor
  · -- Show h has two roots
    use 5, 6
    constructor
    · -- Show h.eval 5 = 0
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
      all_goals norm_num
    · -- Show h.eval 6 = 0
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
      all_goals norm_num
  · -- Show the final logic
    intro h1
    rcases h1 with ⟨x, hx1, h2⟩
    have h3 : ((Polynomial.X^2 - 3 * Polynomial.X + 2) + (Polynomial.X^2 - 7 * Polynomial.X + 12) : Polynomial ℝ).eval x ≠ 0 := by
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
      have h4 : 2 * x ^ 2 - 10 * x + 14 > 0 := by
        nlinarith [sq_nonneg (x - 5 / 2)]
      norm_num
      all_goals nlinarith
    simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X] at hx1 h3
    all_goals
      try { tauto }
      try { nlinarith }