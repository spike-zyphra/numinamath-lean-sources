import Mathlib

theorem number_theory_96423 :
    IsGreatest {a : ℕ | ∃ b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a < 2 * b ∧ b < 3 * c ∧ c < 4 * d ∧ d < 100} 2367 := by 
  constructor 
  · -- Show that 2367 is in the set
    use 1184, 395, 99
    all_goals norm_num
  · -- Show that for any a in the set, a ≤ 2367
    intro a ha
    rcases ha with ⟨b, c, d, ha1, hb1, hc1, hd1, h1, h2, h3, h4⟩
    have h5 : d < 100 := h4
    have h6 : c < 4 * d := by linarith
    have h8 : c ≤ 395 := by
      omega
    have h9 : b ≤ 1184 := by 
      omega
    have h10 : a < 2 * b := h1
    omega