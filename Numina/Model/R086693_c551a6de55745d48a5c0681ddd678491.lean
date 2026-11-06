import Mathlib

open Real

theorem number_theory_212952 (a : ℝ) (ha : 0 < a) :
    IsGreatest {x | ∃ y, x = y^2 ∧ y ≥ 0 ∧ y ≤ a / sqrt 2} (a^2 / 2) := by
  constructor
  · -- this side needs to show the existence of y such that y ≥ 0 and y^2 = a^2 / 2 and y ≤ a / sqrt 2
    use a / sqrt 2
    constructor
    · -- Show that a^2 / 2 = (a / sqrt 2)^2
      have h1 : (a / sqrt 2) ^ 2 = a^2 / 2 := by
        field_simp
        <;> ring_nf <;> norm_num
      linarith [h1]
    constructor
    · -- Show that a / sqrt 2 ≥ 0
      apply div_nonneg
      · linarith
      · positivity
    · -- Show that a / sqrt 2 ≤ a / sqrt 2
      all_goals rfl
  · -- Show that if $x \in \{x | ∃ y, x = y^2 ∧ y \geq 0 ∧ y \leq a / sqrt 2\}$, then $x \leq a^2 / 2$
    intro x hx
    rcases hx with ⟨y, hyeq, hyge, hyle⟩
    have h1 : y ≤ a / sqrt 2 := hyle
    have h2 : y ≥ 0 := hyge
    have h3 : (a / sqrt 2) ^ 2 = a^2 / 2 := by
      field_simp
      <;> ring_nf <;> norm_num
    nlinarith [sq_nonneg (a), sq_nonneg (y), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]