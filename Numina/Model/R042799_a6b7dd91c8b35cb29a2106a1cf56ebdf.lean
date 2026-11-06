import Mathlib

theorem algebra_6744 (a : ℤ) :
    ∃ x : ℝ, a * x ^ 2 + (a + 2) * x + a + 4 = 0 ↔ a = -4 ∨ a = -3 ∨ a = -2 ∨ a = -1 ∨ a = 0 := by
  by_cases h1 : a = -4 ∨ a = -3 ∨ a = -2 ∨ a = -1 ∨ a = 0
  · -- If a is in the set { -4, -3, -2, -1, 0 }, we need to find a real root x.
    rcases h1 with (rfl | rfl | rfl | rfl | rfl)
    · -- a = -4
      use 0
      norm_num
    · -- a = -3
      use (-1 + Real.sqrt 13) / 6
      field_simp
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    · -- a = -2
      use 1
      norm_num
    · -- a = -1
      use (1 + Real.sqrt 13) / 2
      field_simp
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    · -- a = 0
      use -2
      norm_num
  · -- If a is NOT in the set { -4, -3, -2, -1, 0 }, we need to show that the quadratic has no real roots.
    have ha1 : ¬ (a = -4 ∨ a = -3 ∨ a = -2 ∨ a = -1 ∨ a = 0) := by
      simpa using h1
    use 0
    constructor
    · -- Forward: If 0 is a root, then a = -4 ∨ a = -3 ∨ a = -2 ∨ a = -1 ∨ a = 0.
      intro h
      have ha0 : (a : ℝ) + 4 = 0 := by 
        nlinarith
      have ha00 : a = -4 := by
        have h2 : (a : ℝ) = -4 := by linarith
        exact_mod_cast h2
      have ha01 : a = -4 := ha00
      have ha02 : a = -4 ∨ a = -3 ∨ a = -2 ∨ a = -1 ∨ a = 0 := by 
        simp [ha01]
      tauto
    · -- Backward: If a = -4 ∨ a = -3 ∨ a = -2 ∨ a = -1 ∨ a = 0, then 0 is a root.
      intro h
      exfalso
      apply ha1
      exact h