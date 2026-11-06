import Mathlib

theorem algebra_402 :
    IsLeast {x : ℤ | ∃ a b c d : ℤ, a = 2 * b + 8 ∧ b = 3 * c - 18 ∧ c = 5 * d + 10 ∧ x = |d + 7 * a|} 13 := by 
  constructor
  · -- Show that 13 is in the set
    use 2, -3, 5, -1
    all_goals
      norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Show that 13 is the least (i.e., for all x in the set, 13 ≤ x)
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hx⟩
    have h1 : a = 2 * b + 8 := by linarith [ha]
    have h2 : b = 3 * c - 18 := by linarith [hb]
    have h3 : c = 5 * d + 10 := by linarith [hc]
    have eq_b : b = 15 * d + 12 := by 
      rw [h3] at h2
      linarith
    have eq_a : a = 30 * d + 32 := by 
      rw [eq_b] at h1
      linarith
    have eq_d7a : d + 7 * a = 211 * d + 224 := by 
      rw [eq_a]
      linarith
    rw [eq_d7a] at hx
    by_contra h
    push_neg at h
    have h8 : |211 * d + 224| < 13 := by 
      linarith [hx, h]
    have h9 : -13 < (211 * d + 224) := by 
      cases' abs_lt.mp h8 with h10 h11
      linarith
    have h10 : (211 * d + 224) < 13 := by 
      cases' abs_lt.mp h8 with h10 h11
      linarith
    omega