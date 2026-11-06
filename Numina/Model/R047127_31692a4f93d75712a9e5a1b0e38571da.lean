import Mathlib
theorem number_theory_93352 : IsLeast {n | ∃ a b c, a > 0 ∧ b > 0 ∧ c > 0 ∧ 12 * a = 14 * b ∧ 14 * b = 15 * c ∧ 15 * c = n * 20} 21 := by
  constructor
  · -- Show that 21 is in the set
    use 35, 30, 28
    all_goals norm_num
  · -- Show that no smaller n is in the set
    intro n hn
    rcases hn with ⟨a, b, c, ha, hb, hc, h1, h2, h3⟩
    by_contra h
    push_neg at h
    have h4 : n ≤ 20 := by omega
    have h5 : 12 * a = 14 * b := by linarith
    have h6 : 14 * b = 15 * c := by linarith
    have h7 : 15 * c = n * 20 := by linarith
    have h8 : n * 20 ≤ 400 := by 
      nlinarith 
    have h9 : 15 * c ≤ 400 := by 
      linarith [h7, h8]
    have h10 : 14 * b ≤ 400 := by 
      nlinarith [show 14 * b = 15 * c by omega, h9]
    have h11 : 12 * a ≤ 400 := by 
      nlinarith [show 12 * a = 14 * b by omega, h10]
    omega