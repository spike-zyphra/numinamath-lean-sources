import Mathlib

theorem algebra_198837 (x : ℝ) :
    ∃ a b c : ℤ, 2*x-3=a ∧ 5*x-14=b ∧ (2*x-3)/(5*x-14)=c ↔ x=3 := by
  use 3, 1, 3
  constructor
  · -- Assume all are integers, prove x = 3
    rintro ⟨ha, hb, hc⟩
    have h1 : 2 * x - 3 = (3 : ℝ) := by
      norm_num
      exact_mod_cast ha
    have h2 : 5 * x - 14 = (1 : ℝ) := by
      norm_num
      exact_mod_cast hb
    linarith
  · -- Assume x = 3, prove all are integers
    intro hx
    rw [hx]
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num