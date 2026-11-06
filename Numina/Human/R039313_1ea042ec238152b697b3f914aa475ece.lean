import Mathlib.Data.Int.Defs
import Mathlib.Tactic

open Int

/- Find all pairs of integers $(x, y)$ satisfying $x^{2}=y^{2}+y+1$ -/
theorem number_theory_104530 (x y : ℤ) : x^2 = y^2 + y + 1 ↔ (x = -1 ∧ y = -1) ∨ (x = -1 ∧ y = 0) ∨ (x = 1 ∧ y = -1) ∨ (x = 1 ∧ y = 0) := by
  constructor
  · -- Find all possible solutions
    intro hx
    -- Show that y is positive, zero, -1, or less than -1
    have y_cases : 0 < y ∨ y = 0 ∨ y = -1 ∨ y < - 1 := by
      have : y < 0 ∨ y = 0 ∨ 0 < y := Int.lt_trichotomy y 0
      have : y < 0 ↔ y ≤ -1 := by rw [show -1 = 0 - 1 by simp]; exact Iff.symm le_sub_one_iff
      have : y ≤ -1 → y = -1 ∨ y < -1 := fun a => (fun {a b} => Int.le_iff_eq_or_lt.mp) a
      tauto
    rcases y_cases with hy | hy | hy | hy
    · -- Prove that the case 0 < y is impossible
      exfalso
      -- Sandwich x^2 between two consecutive squares
      have sq_sandwich : y^2 < y^2 + y + 1 ∧ y^2 + y + 1 < (y + 1)^2 := ⟨by linarith, by linarith⟩
      rw [← hx] at sq_sandwich
      rcases sq_sandwich with ⟨lb, ub⟩
      rw [sq_lt_sq, show |y| = y by apply abs_eq_self.mpr; positivity] at lb
      rw [sq_lt_sq, show |y + 1| = y + 1 by apply abs_eq_self.mpr; positivity] at ub
      linarith
    · -- Find solutions when y = 0
      rw [hy]
      rw [hy] at hx
      simp at hx
      tauto
    · -- Find solutions when y = -1
      rw [hy]
      rw [hy] at hx
      simp at hx
      tauto
    -- Prove that the case y < -1 is impossible
    exfalso
    -- Sandwich x^2 between two consecutive squares
    have sq_sandwich : (y + 1)^2 < y^2 + y + 1 ∧ y^2 + y + 1 < y^2 := ⟨by linarith, by linarith⟩
    rw [← hx] at sq_sandwich
    rcases sq_sandwich with ⟨lb, ub⟩
    rw [sq_lt_sq, show |y + 1| = -(y + 1) by apply abs_eq_neg_self.mpr; linarith] at lb
    rw [sq_lt_sq, show |y| = -y by apply abs_eq_neg_self.mpr; linarith] at ub
    linarith
  -- Check that all solutions work
  intro h
  rcases h with h | h | h | h
  all_goals
    rcases h with ⟨hx, hy⟩
    rw [hx, hy]
    norm_num