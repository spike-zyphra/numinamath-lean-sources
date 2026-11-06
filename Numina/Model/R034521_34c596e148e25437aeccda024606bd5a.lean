import Mathlib

theorem number_theory_107211 (a : ℝ) (ha : Irrational a) :
    ∃! m : ℤ, ∃ x1 x2 : ℚ, x1 ≠ x2 ∧ (x1 * a - x2 * 0 = m * (x1 - x2)) := by
  use 0
  constructor
  · -- First, we prove that m = 0 works by exhibiting rational points x1 and x2
    use (0 : ℚ), (1 : ℚ)
    constructor
    · -- Show that 0 ≠ 1
      norm_num
    · -- Verify that 0 * a - 1 * 0 = 0 * (0 - 1)
      norm_num
  · -- Now, prove that if another m works, it must be 0
    intro m
    rintro ⟨x1, x2, h12, heq⟩
    have heq' : (x1 : ℝ) * a = (m : ℝ) * ((x1 : ℝ) - (x2 : ℝ)) := by
      norm_num at heq ⊢
      linarith
    by_cases hx1 : (x1 : ℚ) = (0 : ℚ)
    · -- Case where x1 = 0
      rw [show (x1 : ℝ) = (0 : ℝ) by exact_mod_cast hx1] at heq'
      have hx2' : x2 ≠ (0 : ℚ) := by
        intro h
        apply h12
        rw [hx1, h]
        all_goals norm_num
      have eq1 : (m : ℝ) * (x2 : ℝ) = 0 := by
        nlinarith
      have eq2 : (m : ℝ) = 0 ∨ (x2 : ℝ) = 0 := by
        apply mul_eq_zero.mp
        exact eq1
      rcases eq2 with (h | h)
      · -- Case where m = 0
        have : (m : ℤ) = 0 := by
          exact_mod_cast h
        exact_mod_cast this
      · -- Case where x2 = 0, which contradicts hx2'
        have h2 : (x2 : ℝ) = (0 : ℝ) := by
          exact h
        have h3 : (x2 : ℚ) = (0 : ℚ) := by
          exact_mod_cast h2
        contradiction
    · -- Case where x1 ≠ 0
      have eqn : (a : ℝ) = (m : ℝ) - ((m : ℝ) * (x2 : ℝ) / (x1 : ℝ)) := by
        have h1 : (x1 : ℝ) ≠ 0 := by
          exact_mod_cast hx1
        field_simp at *
        linarith
      have h2 : ¬ Irrational (a : ℝ) := by
        rw [eqn]
        simp [show (m : ℝ) = (m : ℤ) by simp, show (x1 : ℝ) = (x1 : ℚ) by simp, show (x2 : ℝ) = (x2 : ℚ) by simp]
      contradiction