import Mathlib

theorem number_theory_6832 (x : ℤ) (hx : 7 * x ≡ 107 [ZMOD 11]) :
    IsLeast {y | ∃ x : ℤ, 7 * x ≡ 107 [ZMOD 11] ∧ |x| = y} 2 := by
  constructor
  · -- Show 2 is in the set
    use -2
    native_decide
  · -- Show no element less than 2 is in the set
    intro y hy
    rcases hy with ⟨x, hx, hxy⟩
    by_contra h
    push_neg at h
    have h2 : |x| < (2 : ℤ) := by linarith
    have h3 : x = 0 ∨ x = 1 ∨ x = -1 := by 
      cases' abs_cases x with h h <;> omega
    norm_num [Int.ModEq] at hx
    rcases h3 with (rfl | rfl | rfl)
    all_goals omega