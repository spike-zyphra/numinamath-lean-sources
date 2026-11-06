import Mathlib

open Finset

theorem combinatorics_609441 : IsGreatest {k : ℕ | ∃ x y : ℕ, k = abs (x - 1007 : ℤ) + abs (y - 1007 : ℤ) ∧ x < 2015 ∧ y < 2015} 2014 := by
  constructor
  · simp
    use 0, 0
    norm_num
  · intro d hd
    simp at hd
    rcases hd with ⟨x, y, hd, hx₁, hy₁⟩
    have hx₂ : |(x - 1007 : ℤ)| ≤ 1007 := by
      obtain (h | h) := abs_choice (x - 1007 : ℤ) <;>
        rw [h] <;>
        field_simp
      norm_num
      linarith
    have hy₂ : |(y - 1007 : ℤ)| ≤ 1007 := by
      obtain (h | h) := abs_choice (y - 1007 : ℤ) <;>
        rw [h] <;>
        field_simp
      norm_num
      linarith
    suffices abs (x - 1007 : ℤ) + abs (y - 1007 : ℤ) ≤ 2014 by
      rw [hd.symm] at this
      norm_cast at this
    linarith
