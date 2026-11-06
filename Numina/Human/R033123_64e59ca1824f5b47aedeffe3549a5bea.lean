import Mathlib



/-
The solution to the equation $\log_{5}(x+2) - \log_{5}(3x-4) = -\log_{5}(x-2)$ is.
-/

theorem algebra_9163 {x : ℝ} (hx : x ≠ 2 ∧ x ≠ -2 ∧ 0 < x + 2 ∧ 0 < 3 * x - 4 ∧ 0 < x - 2) :
    Real.logb 5 (x + 2) - Real.logb 5 (3 * x - 4) = -Real.logb 5 (x - 2) ↔ x = 3 := by
  obtain ⟨hxne2, hxneneg2, _⟩ := hx

  -- aux lemma, if $\log_5^a = \log_5 b$, then $a = b$.
  have l_logbeq_if {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Real.logb 5 a = Real.logb 5 b → a = b := by
    intro h
    apply (Real.logb_eq_iff_rpow_eq (show 0 < 5 by norm_num) (by norm_num) ha).mp at h
    rw [Real.rpow_logb] at h
    all_goals linarith

  constructor

  . intro h

    have r_ne1 : x + 2 ≠ 0 := by
      apply (add_ne_add_left 2).mpr at hxneneg2
      rw [neg_add_cancel] at hxneneg2
      exact hxneneg2

    have r_ne2 : x - 2 ≠ 0 := by
      exact sub_ne_zero_of_ne hxne2

    have r_ineq1 : 0 < (x + 2) * (x - 2) := by
      apply mul_pos
      all_goals linarith

    have r_ineq2 : 0 < 3 * x - 4 := by
      linarith

    have : Real.logb 5 (x + 2) + Real.logb 5 (x - 2) = Real.logb 5 (3 * x - 4) := by
      rw [← sub_add_cancel (Real.logb 5 (x + 2)) (Real.logb 5 (3 * x - 4)),
          h, neg_add_cancel_comm]

    rw [← Real.logb_mul (r_ne1) (r_ne2)] at this
    apply l_logbeq_if r_ineq1 r_ineq2 at this

    -- we get $(x + 2) * (x - 2) = 3 * x - 4$,
    -- then $x ^ 2 - 4 = 3 * x - 4$, $x = 0 \or x = 3$,
    rw [show (x + 2) * (x - 2) = x ^ 2 - 4 by ring, pow_two] at this
    simp at this

    -- since $x - 2 > 0$, we get $x = 0$
    rcases this with hxeq3 | hxeq0
    . exact hxeq3
    . linarith

  .
    -- verify that x = 3 is a solution
    intro hxeq3
    simp [hxeq3]
    norm_num
