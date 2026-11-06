import Mathlib

open Real

theorem inequalities_127135 {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range (n ^ 2), (sqrt (i + 1)) % 1 ≤ (n ^ 2 - 1) / 2 := by
  have h1 : ∀ (i : ℕ), (sqrt (i + 1)) % 1 = 0 := by
    intro i
    have h2 : sqrt (i + 1) = Real.sqrt ((i + 1 : ℝ)) := by rfl
    simp [h2, Nat.sqrt]
  have h3 : ∑ i in Finset.range (n ^ 2), (sqrt (i + 1)) % 1 = (0 : ℝ) := by
    have h4 : ∀ (i : ℕ), (sqrt (i + 1)) % 1 = (0 : ℝ) := h1
    rw [Finset.sum_eq_zero]
    intro i hi
    specialize h4 i
    simpa using h4
  have h4 : (0 : ℝ) ≤ (n ^ 2 - 1 : ℝ) / 2 := by
    have h5 : (n : ℝ) ≥ 1 := by
      exact_mod_cast show (1 : ℝ) ≤ (n : ℝ) by
        have h6 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show n ≥ 1 by omega)
        nlinarith
    have h7 : (n ^ 2 : ℝ) ≥ 1 := by
      nlinarith [sq_nonneg (n : ℝ), sq_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast show 0 < (n : ℕ) by linarith)]
    have h8 : (n ^ 2 - 1 : ℝ) ≥ 0 := by
      nlinarith
    have h9 : (n ^ 2 - 1 : ℝ) / 2 ≥ 0 := by
      apply div_nonneg
      linarith
      norm_num
    linarith
  linarith [h3, h4]