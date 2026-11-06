import Mathlib

theorem algebra_108784 {a b c : ℝ} (ha : a > 0) (h1 : |a + b + c| = 4) (h2 : |4*a + 2*b + c| = 4)
    (h3 : |9*a + 3*b + c| = 4) :
    (a = 8 ∧ b = -32 ∧ c = 28) ∨ (a = 4 ∧ b = -20 ∧ c = 20) ∨
    (a = 4 ∧ b = -12 ∧ c = 4) := by
  cases' abs_cases (a + b + c) with h11 h11
  · -- Case where a + b + c ≥ 0, so |a + b + c| = a + b + c
    cases' abs_cases (4*a + 2*b + c) with h21 h21
    · -- Case where 4*a + 2*b + c ≥ 0, so |4*a + 2*b + c| = 4*a + 2*b + c
      cases' abs_cases (9*a + 3*b + c) with h31 h31
      · -- Case where 9*a + 3*b + c ≥ 0, so |9*a + 3*b + c| = 9*a + 3*b + c
        exfalso
        nlinarith 
      · -- Case where 9*a + 3*b + c < 0, so |9*a + 3*b + c| = -(9*a + 3*b + c)
        exfalso
        nlinarith 
    · -- Case where 4*a + 2*b + c < 0, so |4*a + 2*b + c| = -(4*a + 2*b + c)
      cases' abs_cases (9*a + 3*b + c) with h31 h31
      · -- Case where 9*a + 3*b + c ≥ 0, so |9*a + 3*b + c| = 9*a + 3*b + c
        left 
        constructor
        · -- Show that a = 8
          linarith 
        constructor
        · -- Show that b = -32
          linarith 
        · -- Show that c = 28
          linarith 
      · -- Case where 9*a + 3*b + c < 0, so |9*a + 3*b + c| = -(9*a + 3*b + c)
        right 
        left 
        constructor
        · -- Show that a = 4
          linarith 
        constructor
        · -- Show that b = -20
          linarith 
        · -- Show that c = 20
          linarith 
  · -- Case where a + b + c < 0, so |a + b + c| = -(a + b + c)
    cases' abs_cases (4*a + 2*b + c) with h21 h21
    · -- Case where 4*a + 2*b + c ≥ 0, so |4*a + 2*b + c| = 4*a + 2*b + c
      cases' abs_cases (9*a + 3*b + c) with h31 h31
      · -- Case where 9*a + 3*b + c ≥ 0, so |9*a + 3*b + c| = 9*a + 3*b + c
        exfalso
        nlinarith 
      · -- Case where 9*a + 3*b + c < 0, so |9*a + 3*b + c| = -(9*a + 3*b + c)
        exfalso
        nlinarith 
    · -- Case where 4*a + 2*b + c < 0, so |4*a + 2*b + c| = -(4*a + 2*b + c)
      cases' abs_cases (9*a + 3*b + c) with h31 h31
      · -- Case where 9*a + 3*b + c ≥ 0, so |9*a + 3*b + c| = 9*a + 3*b + c
        right
        right
        constructor
        · -- Show that a = 4
          linarith 
        constructor
        · -- Show that b = -12
          linarith 
        · -- Show that c = 4
          linarith 
      · -- Case where 9*a + 3*b + c < 0, so |9*a + 3*b + c| = -(9*a + 3*b + c)
        exfalso
        nlinarith