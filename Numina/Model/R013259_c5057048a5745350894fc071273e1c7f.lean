import Mathlib

theorem algebra_8833 (x : ℝ) :
    (x ^ 2 + 3 * x - 4)^3 + (2 * x^2 - 5 * x + 3)^3 =
    (3 * x^2 - 2 * x - 1)^3 ↔
    x = -4 ∨ x = -1 / 3 ∨ x = 1 ∨ x = 3 / 2 := by
  constructor
  · -- Forward direction
    intro h 
    have h1 : (x ^ 2 + 3 * x - 4) + (2 * x^2 - 5 * x + 3) = 3 * x ^ 2 - 2 * x - 1 := by 
      ring
    have h2 : (x ^ 2 + 3 * x - 4)^3 + (2 * x^2 - 5 * x + 3)^3 - (3 * x^2 - 2 * x - 1)^3 = 0 := by linarith [h]
    have h3 : 3 * (x ^ 2 + 3 * x - 4) * (2 * x^2 - 5 * x + 3) * (3 * x^2 - 2 * x - 1) = 0 := by 
      nlinarith [sq_nonneg (x ^ 2 + 3 * x - 4 - (2 * x^2 - 5 * x + 3)), sq_nonneg ((2 * x^2 - 5 * x + 3) - (3 * x^2 - 2 * x - 1)), sq_nonneg ((x ^ 2 + 3 * x - 4) + (2 * x^2 - 5 * x + 3) + (3 * x^2 - 2 * x - 1)), sq_nonneg (x ^ 2 + 3 * x - 4 - (3 * x^2 - 2 * x - 1)), sq_nonneg ((x) * 1)]
    cases' (mul_eq_zero.mp h3) with h31 h32
    · -- Case $h31 : 3 * (x ^ 2 + 3 * x - 4) * (2 * x^2 - 5 * x + 3) = 0$
      cases' (mul_eq_zero.mp h31) with h311 h312
      · -- Case $h311 : 3 * (x ^ 2 + 3 * x - 4) = 0$
        have h41 : x ^ 2 + 3 * x - 4 = 0 := by 
          have h42 : 3 * (x ^ 2 + 3 * x - 4) = 0 := by 
            linarith [h311]
          linarith
        have h42 : (x - 1) * (x + 4) = 0 := by
          nlinarith [h41] 
        cases' (mul_eq_zero.mp h42) with h43 h44
        · -- Case where $x - 1 = 0$. 
          right 
          right 
          left 
          linarith 
        · -- Case $x + 4 = 0$. 
          left 
          linarith 
      · -- Case $h312 : 2 * x ^ 2 - 5 * x + 3 = 0$
        have h34 : 2 * x ^ 2 - 5 * x + 3 = 0 := by
          linarith [h312]
        have h35 : (x - 1) * (2 * x - 3) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.mp h35) with h36 h37
        · -- Case $x - 1 = 0$. 
          right 
          right 
          left 
          linarith 
        · -- Case $2x - 3 = 0$. 
          right 
          right 
          right 
          linarith 
    · -- Case $h32 : (3 * x^2 - 2 * x - 1) = 0$
      have h33 : 3 * x^2 - 2 * x - 1 = 0 := by linarith [h32]
      have h34 : (x - 1) * (3 * x + 1) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h34) with h35 h36
      · -- Case where $x - 1 = 0$ so $x = 1$.
        right 
        right 
        left 
        linarith 
      · -- Case $3x + 1 = 0$ so $x = -1/3$. 
        right 
        left 
        linarith 
  · -- Backward direction: show the roots satisfy the equation
    rintro (h | h | h | h)
    · -- Case x = -4
      rw [h]
      norm_num 
    · -- Case x = -1 / 3
      rw [h]
      norm_num 
    · -- Case x = 1
      rw [h]
      norm_num 
    · -- Case x = 3 / 2
      rw [h]
      norm_num