import Mathlib

theorem algebra_114799 (x y : ℤ) :
    2*x^2-2*x*y+9*x+y=2 ↔
    (x=1 ∧ y=9) ∨ (x=2 ∧ y=8) ∨ (x=0 ∧ y=2) ∨ (x=-1 ∧ y=3) := by
  constructor
  · -- Forward direction: given (x, y) satisfies the equation, derive the four possible pairs
    intro h_eq
    have h_eq2 : 2*x^2 - 2*x*y + 9*x + y = 2 := h_eq
    have h_eq3 : (1 - 2*x) * (y - (x + 5)) = -3 := by
      nlinarith
    have h_divides : 1 - 2*x ∣ -3 := by
      use y - (x + 5)
      linarith
    have h_divides' : 1 - 2*x ∣ 3 := by
      exact Int.dvd_neg.mp h_divides
    have h_self_eq : (1 - 2*x) = 1 ∨ (1 - 2*x) = 3 ∨ (1 - 2*x) = -1 ∨ (1 - 2*x) = -3 := by
      have h4 : (1 - 2*x) ∣ 3 := by exact h_divides'
      have h5 : (1 - 2*x) ≤ 3 := by
        exact Int.le_of_dvd (show (0 : ℤ) < 3 by norm_num) h4
      have h6 : (1 - 2*x) ≥ -3 := by 
        have h7 : -(1 - 2*x) ∣ 3 := by
          exact Int.neg_dvd.2 h4
        have h8 : -(1 - 2*x) ≤ 3 := by 
          exact Int.le_of_dvd (show (0 : ℤ) < 3 by norm_num) h7
        linarith
      interval_cases k : (1 - 2*x) <;> omega
    rcases h_self_eq with h_self_eq1 | h_self_eq3 | h_self_neg_eq1 | h_self_neg_eq3
    · -- Case 1: $1 - 2x = 1$, so $x = 0$
      have hx_eq0 : x = 0 := by
        nlinarith
      have hy_eq2 : y = 2 := by
        nlinarith [h_eq3, h_self_eq1]
      exact Or.inr (Or.inr (Or.inl ⟨hx_eq0, hy_eq2⟩))
    · -- Case 2: $1 - 2x = 3$, so $x = -1$
      have hx_eq_neg1 : x = -1 := by
        nlinarith
      have hy_eq3 : y = 3 := by
        nlinarith [h_eq3, h_self_eq3]
      exact Or.inr (Or.inr (Or.inr ⟨hx_eq_neg1, hy_eq3⟩))
    · -- Case 3: $1 - 2x = -1$, so $x = 1$
      have hx_eq1 : x = 1 := by
        nlinarith
      have hy_eq9 : y = 9 := by
        nlinarith [h_eq3, h_self_neg_eq1]
      exact Or.inl ⟨hx_eq1, hy_eq9⟩
    · -- Case 4: $1 - 2x = -3$, so $x = 2$
      have hx_eq2 : x = 2 := by
        nlinarith
      have hy_eq8 : y = 8 := by
        nlinarith [h_eq3, h_self_neg_eq3]
      exact Or.inr (Or.inl ⟨hx_eq2, hy_eq8⟩)
  · -- Backward direction: given the four possible pairs, verify they satisfy the equation
    rintro (h | h | h | h)
    · -- Case (1, 9)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (2, 8)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (0, 2)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (-1, 3)
      rcases h with ⟨rfl, rfl⟩
      norm_num