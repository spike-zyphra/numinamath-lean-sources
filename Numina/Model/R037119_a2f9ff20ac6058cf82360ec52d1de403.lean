import Mathlib

theorem number_theory_100684 : 3 = (Nat.floor (Real.sqrt 10)) := by
  have h1 : Nat.floor (Real.sqrt 10) = 3 := by
    have h2 : 3 ≤ Real.sqrt 10 := by
      rw [Real.le_sqrt] <;> norm_num
    have h3 : Real.sqrt 10 < (4 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    have h4 : Nat.floor (Real.sqrt 10) = 3 := by
      simp [Nat.floor_eq_iff]
      constructor <;> (try norm_num) <;> linarith
    exact h4
  linarith