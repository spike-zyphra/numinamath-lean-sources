import Mathlib
open Nat Real Finset Set
noncomputable section

/-11. If the function $y=\lg \left(x^{2}-a x+a\right)$ has a range of $\mathbf{R}$, then the range of real number $a$ is $\qquad$.-/
theorem algebra_200234 :
    ∀ a : ℝ, (∀ y : ℝ, ∃ x : ℝ, y = Real.log (x^2 - a * x + a) ∧ x^2 - a * x + a > 0) ↔
    (a ≤ 0 ∨ a ≥ 4) := by
  intro a
  constructor
  · -- Forward: If for all real $y$, there exists $x$ satisfy the conditions, then $a ≤ 0 ∨ a ≥ 4$.
    intro h_all_y
    have h_a_range : a ≤ 0 ∨ a ≥ 4 := by
      by_contra h_not_a_range
      -- Assume $a$ is between $0$ and $4$.
      have h_a_bounds : 0 < a ∧ a < 4 := by
        by_cases h_a_le_0 : a ≤ 0
        · exfalso
          exact h_not_a_range (Or.inl h_a_le_0)
        · have h_a_pos : a > 0 := by linarith
          have h_a_lt_4 : a < 4 := by
            by_contra h_a_ge_4_contra
            have h_a_ge_4 : a ≥ 4 := by linarith
            exact h_not_a_range (Or.inr h_a_ge_4)
          exact ⟨h_a_pos, h_a_lt_4⟩
      -- When $0 < a < 4$, the discriminant $a^2 - 4a < 0$.
      have h_a_pos : a > 0 := h_a_bounds.1
      have h_a_lt_4 : a < 4 := h_a_bounds.2
      have h_disc_neg : a ^ 2 - 4 * a < 0 := by
        nlinarith
      -- Since the discriminant is negative, $x^2 - a * x + a$ is always positive.
      have h_quadratic_pos : ∀ x : ℝ, x ^ 2 - a * x + a > 0 := by
        intro x
        nlinarith [sq_nonneg (x - a / 2)]
      -- Prove positivity of $a - a^2 / 4$ and $(a - a^2 / 4) / 2$.
      have h_min_val_pos : a - a ^ 2 / 4 > 0 := by
        have h_rewrite : a - a ^ 2 / 4 = a * (1 - a / 4) := by ring
        have h_factor_pos : 1 - a / 4 > 0 := by linarith
        have h_a_pos_inner : a > 0 := h_a_bounds.1
        rw [h_rewrite]
        apply mul_pos h_a_pos_inner h_factor_pos
      have h_min_val_half_pos : (a - a ^ 2 / 4) / 2 > 0 := by
        apply div_pos h_min_val_pos
        norm_num
      -- Choose $y = Real.log ((a - a^2 / 4) / 2)$.
      have h_exists_x : ∃ x : ℝ, Real.log ((a - a ^ 2 / 4) / 2) = Real.log (x ^ 2 - a * x + a) ∧ x ^ 2 - a * x + a > 0 := by
        apply h_all_y (Real.log ((a - a ^ 2 / 4) / 2))
      obtain ⟨x, h_log_eq, h_val_pos⟩ := h_exists_x
      have h_log_eq_inner : Real.log (x ^ 2 - a * x + a) = Real.log ((a - a ^ 2 / 4) / 2) := by
        linarith
      have h_quadratic_eq : x ^ 2 - a * x + a = (a - a ^ 2 / 4) / 2 := by
        have h_log_eq_restate : Real.log (x ^ 2 - a * x + a) = Real.log ((a - a ^ 2 / 4) / 2) := h_log_eq_inner
        have h_quadratic_pos_inner : x ^ 2 - a * x + a > 0 := h_val_pos
        apply Real.log_injOn_pos (Set.mem_Ioi.mpr h_quadratic_pos_inner) (Set.mem_Ioi.mpr h_min_val_half_pos)
        exact h_log_eq_restate
      -- Prove $x^2 - a * x + a ≥ a - a^2 / 4$.
      have h_complete_square : (x - a / 2) ^ 2 + a - a ^ 2 / 4 = x ^ 2 - a * x + a := by
        nlinarith
      have h_val_ge_min : (x - a / 2) ^ 2 + a - a ^ 2 / 4 ≥ a - a ^ 2 / 4 := by
        nlinarith [sq_nonneg (x - a / 2)]
      -- From h_quadratic_eq and h_complete_square, $x^2 - a * x + a = (a - a^2 / 4) / 2$.
      have h_quadratic_eq_restate : x ^ 2 - a * x + a = (a - a ^ 2 / 4) / 2 := h_quadratic_eq
      -- Contradiction: $x^2 - a * x + a ≥ a - a^2 / 4$ but equals $(a - a^2 / 4) / 2$.
      have h_half_lt_min : (a - a ^ 2 / 4) / 2 < a - a ^ 2 / 4 := by
        have h_diff : a - a ^ 2 / 4 - (a - a ^ 2 / 4) / 2 = (a - a ^ 2 / 4) / 2 := by
          field_simp; ring
        linarith [h_min_val_half_pos]
      have h_contradiction : False := by
        have h_ge_min_val : x ^ 2 - a * x + a ≥ a - a ^ 2 / 4 := by linarith [h_complete_square, h_val_ge_min]
        have h_eq_half_min : x ^ 2 - a * x + a = (a - a ^ 2 / 4) / 2 := h_quadratic_eq_restate
        linarith [h_half_lt_min]
      exact h_contradiction
    exact h_a_range
  · -- Backward: If $a ≤ 0 ∨ a ≥ 4$, then for all real $y$, there exists $x$ satisfy the conditions.
    intro h_a_range
    have h_a_conditions : a ≤ 0 ∨ a ≥ 4 := h_a_range
    have h_forall_y : ∀ y : ℝ, ∃ x : ℝ, y = Real.log (x ^ 2 - a * x + a) ∧ x ^ 2 - a * x + a > 0 := by
      intro y
      have h_a_cases : a ≤ 0 ∨ a ≥ 4 := h_a_conditions
      -- When $a ≤ 0$ or $a ≥ 4$, the discriminant $a^2 - 4a ≥ 0$.
      -- In these cases, $x^2 - a * x + a$ can take all positive real values.
      have h_exists_x : ∃ (x : ℝ), y = Real.log (x ^ 2 - a * x + a) ∧ x ^ 2 - a * x + a > 0 := by
        -- Construct $x$ such that $x^2 - a * x + a = exp y$.
        have h_solve_quadratic : ∃ (x : ℝ), x ^ 2 - a * x + a = Real.exp y := by
          -- Solve the quadratic equation $x^2 - a * x + (a - exp y) = 0$.
          have h_exp_pos : 0 < Real.exp y := Real.exp_pos y
          have h_disc_nonneg : a ^ 2 - 4 * (a - Real.exp y) ≥ 0 := by
            cases h_a_cases with
            | inl h_a_le_0 =>
              -- When $a ≤ 0$.
              nlinarith [sq_nonneg (a - 2), Real.add_one_le_exp y]
            | inr h_a_ge_4 =>
              -- When $a ≥ 4$.
              nlinarith [sq_nonneg (a - 2), Real.add_one_le_exp y]
          -- The quadratic $x^2 - a * x + (a - exp y) = 0$ has discriminant $a^2 - 4 * (a - exp y) ≥ 0$.
          -- Thus, it has real solutions.
          use (a + Real.sqrt (a ^ 2 - 4 * (a - Real.exp y))) / 2
          have h_disc_ge_0 : 0 ≤ a ^ 2 - 4 * (a - Real.exp y) := by linarith
          have h_sqrt_nonneg : 0 ≤ Real.sqrt (a ^ 2 - 4 * (a - Real.exp y)) := Real.sqrt_nonneg _
          nlinarith [Real.sq_sqrt (show 0 ≤ a ^ 2 - 4 * (a - Real.exp y) by linarith),
            Real.add_one_le_exp y]
        obtain ⟨x, h_quadratic_eq⟩ := h_solve_quadratic
        have h_quadratic_pos : x ^ 2 - a * x + a > 0 := by
          have h_eq_exp : x ^ 2 - a * x + a = Real.exp y := by linarith
          have h_exp_pos_inner : Real.exp y > 0 := Real.exp_pos y
          linarith
        refine' ⟨x, _⟩
        constructor
        · -- Prove $y = Real.log (x ^ 2 - a * x + a)$.
          have h_eq_exp : x ^ 2 - a * x + a = Real.exp y := by linarith
          have h_log_y : Real.log (x ^ 2 - a * x + a) = y := by
            rw [h_eq_exp]
            rw [Real.log_exp]
          linarith
        · -- Prove $x ^ 2 - a * x + a > 0$.
          exact h_quadratic_pos
      exact h_exists_x
    exact h_forall_y
