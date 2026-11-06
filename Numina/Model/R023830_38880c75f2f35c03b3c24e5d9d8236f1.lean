import Mathlib

open Real

theorem inequalities_4043 : (Nat.factorial 300 : ℝ) > √(300^300) := by
  have h1 : (Nat.factorial 300 : ℝ) > √(300^300) := by
    have h1 : (Nat.factorial 300 : ℝ) ^ 2 > (300 : ℝ) ^ 300 := by
      have h2 : Nat.factorial 300 ^ 2 > 300 ^ 300 := by
        native_decide
      have h3 : (Nat.factorial 300 : ℝ) ^ 2 > (300 : ℝ) ^ 300 := by
        exact_mod_cast h2
      exact_mod_cast h3
    have h4 : (Nat.factorial 300 : ℝ) > 0 := by
      positivity
    have h5 : (300 : ℝ) ^ 300 ≥ 0 := by
      positivity
    have h20 : (Nat.factorial 300 : ℝ) > Real.sqrt ((300 : ℝ) ^ 300) := by
      have h7 : Real.sqrt ((Nat.factorial 300 : ℝ) ^ 2) > Real.sqrt ((300 : ℝ) ^ 300) := by
        apply Real.sqrt_lt_sqrt
        all_goals nlinarith
      have h8 : Real.sqrt ((Nat.factorial 300 : ℝ) ^ 2) = (Nat.factorial 300 : ℝ) := by
        rw [Real.sqrt_sq (show 0 ≤ (Nat.factorial 300 : ℝ) by positivity)]
      have h9 : Real.sqrt ((300 : ℝ) ^ 300) = Real.sqrt ((300 : ℝ) ^ 300) := by
        rfl
      nlinarith [h7, h8]
    simpa using h20
  exact_mod_cast h1