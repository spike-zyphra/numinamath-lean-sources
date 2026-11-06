import Mathlib

theorem inequalities_40067 (a b c d e : ℝ) (h₀ : a + b < c + d) (h₁ : c + d < e + a)
    (h₂ : e + a < b + c) (h₃ : b + c < d + e) :
    min (min (min (min a b) c) d) e = a ∧ max (max (max (max a b) c) d) e = e := by
  constructor
  · -- Show that a is the minimum
    have ha1 : a < b := by linarith
    have ha2 : a < c := by linarith
    have ha3 : a < d := by linarith
    have ha4 : a < e := by linarith
    have h1 : min (min (min (min a b) c) d) e = a := by
      have h1 : a ≤ b := by linarith
      have h2 : a ≤ c := by linarith
      have h3 : a ≤ d := by linarith
      have h4 : a ≤ e := by linarith
      simp [min_eq_left_of_lt, h1, h2, h3, h4, ha1, ha2, ha3, ha4]
      all_goals linarith
    exact h1
  · -- Show that e is the maximum
    have he1 : e > a := by linarith
    have he2 : e > b := by linarith
    have he3 : e > c := by linarith
    have he4 : e > d := by linarith
    have h2 : max (max (max (max a b) c) d) e = e := by
      have h1 : a ≤ e := by linarith
      have h2 : b ≤ e := by linarith
      have h3 : c ≤ e := by linarith
      have h4 : d ≤ e := by linarith
      simp [max_eq_right_of_lt, h1, h2, h3, h4]
      all_goals linarith
    exact h2