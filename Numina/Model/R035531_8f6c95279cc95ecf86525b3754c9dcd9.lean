import Mathlib

theorem algebra_2833 (a : ℤ) (x y : ℤ) (h : x ^ 2 - x * y - a * x + a * y + 1 = 0) :
    x - y = 1 ∨ x - y = -1 := by
  have h1 : (x - y) * (x - a) = -1 := by
    nlinarith
  have h3 : (x - y) = 1 ∨ (x - y) = -1 := by
    have h4 : (x - y) * (x - a) = -1 := h1
    have h5 : (x - y) ∣ -1 := by
      use (x - a)
      all_goals linarith
    have h6 : (x - y) ∣ 1 := by 
      exact Int.dvd_neg.mp h5
    have h7 : (x - y) = 1 ∨ (x - y) = -1 := by
      have h8 : (x - y) ≤ 1 := by
        apply Int.le_of_dvd (by norm_num) h6
      have h9 : (x - y) ≥ -1 := by
        have h10 : (- (x - y)) ∣ 1 := by
          exact Int.neg_dvd.2 h6
        have h11 : - (x - y) ≤ 1 := by 
          apply Int.le_of_dvd (by norm_num) h10
        omega
      interval_cases (x - y) <;> tauto
    exact h7
  cases h3 with
  | inl h4 =>
    left
    exact h4
  | inr h4 =>
    right
    exact h4