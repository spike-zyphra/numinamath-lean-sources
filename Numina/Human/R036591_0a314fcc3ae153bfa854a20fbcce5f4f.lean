import Mathlib

theorem inequalities_197809 (a : ℝ) :
    (∀ x : ℝ, x ^ 2 - 2 ^ (a + 2) * x - 2 ^ (a + 3) + 12 > 0) ↔ a < 0 := by
  constructor
  · intro h
    contrapose! h
    use 2 ^ (a + 1)
    suffices ((2 : ℝ) ^ a + 3) * (2 ^ a - 1) ≥ 0 by
      iterate 3 rw [Real.rpow_add (by norm_num)]
      linarith only [this]
    apply mul_nonneg
    . positivity
    . simp
      apply Real.one_le_rpow (by norm_num)
      exact h
  · intro h x
    suffices (x - 2 ^ (a + 1)) ^ 2 > 4 * (2 ^ a + 3) * (2 ^ a - 1) by
      rw [Real.rpow_add (by norm_num)] at this
      iterate 2 rw [Real.rpow_add (by norm_num)]
      linarith only [this]
    calc
      _ ≥ (0 : ℝ) := by apply sq_nonneg
      _ > (4 * (2 ^ a + 3) * (2 ^ a - 1)) := by
        apply mul_neg_of_pos_of_neg
        . positivity
        . simp
          apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
          exact h
