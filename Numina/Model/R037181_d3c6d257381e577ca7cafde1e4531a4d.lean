import Mathlib

open Finset

theorem number_theory_16746  :
    IsGreatest {k : ℕ | ∃ a b c y : ℤ, y ∈ Ioc 0 9 ∧ a ∈ Icc 0 9 ∧ b ∈ Icc 0 9 ∧ c ∈ Icc 0 9 ∧ 
    (1 : ℝ) / y = a / 10 + b / 100 + c / 1000 ∧ k = a + b + c} 8:= by
  constructor
  · -- Show 8 is in the set.
    use 1, 2, 5, 8
    norm_num [Finset.mem_Icc, Finset.mem_Ioc]
  · -- Show that 8 is greatest.
    intro k hk
    rcases hk with ⟨a, b, c, y, hy, ha, hb, hc, h_eq, hk⟩
    rw [Finset.mem_Ioc] at hy
    rw [Finset.mem_Icc] at ha hb hc
    rcases ha with ⟨ha0, ha1⟩
    rcases hb with ⟨hb0, hb1⟩
    rcases hc with ⟨hc0, hc1⟩
    have y_pos : y > 0 := hy.1
    have y_le_9 : y ≤ 9 := hy.2
    have h_eq1 : (1 : ℝ) / (y : ℝ) = (a : ℝ) / 10 + (b : ℝ) / 100 + (c : ℝ) / 1000 := by
      simpa using h_eq
    have eq1 : (1 : ℝ) = ( (a : ℝ) / 10 + (b : ℝ) / 100 + (c : ℝ) / 1000 ) * (y : ℝ) := by
      have h6 : (y : ℝ) > 0 := by
        have : (y : ℝ) > 0 := by
          exact_mod_cast hy.1
        linarith
      field_simp at h_eq1 ⊢
      nlinarith
    have eq5 : (1000 : ℝ) = (100 * (a : ℝ) + 10 * (b : ℝ) + (c : ℝ)) * (y : ℝ) := by
      nlinarith [eq1]
    have eq4 : (1000 : ℤ) = (100 * a + 10 * b + c) * y := by
      exact_mod_cast eq5
    interval_cases y <;> norm_num at eq4 
    <;> omega