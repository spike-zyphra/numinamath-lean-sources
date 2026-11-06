import Mathlib

theorem inequalities_169690 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c + 2 = a * b * c) :
    (a + 1) * (b + 1) * (c + 1) ≥ 27 ∧
    ((a + 1) * (b + 1) * (c + 1) = 27 ↔ a = b ∧ b = c ∧ c = 2) := by 
  have h1 : (a + 1) * (b + 1) * (c + 1) = a * b * c + a * b + a * c + b * c + a + b + c + 1 := by
    ring
  have h2 : a * b * c = a + b + c + 2 := by
    linarith
  have h3 : (a + 1) * (b + 1) * (c + 1) = (a * b + a * c + b * c) + 2 * (a + b + c) + 3 := by 
    rw [h1]
    rw [show a * b * c = a + b + c + 2 by linarith [h2]]
    all_goals
      nlinarith
  have h4 : (a * b + a * c + b * c) + 2 * (a + b + c) + 3 ≥ 27 := by
    nlinarith [sq_nonneg (a - 2 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (c - 2 : ℤ), 
          h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
  constructor
  · -- First part: inequality
    nlinarith [h3, h4]
  · -- Second part: iff statement
    constructor
    · -- Forward
      intro h_eq
      have h11 : a ≤ 5 := by
        nlinarith [sq_nonneg (a - 2 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (c - 2 : ℤ), 
            h_eq, h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
      have h12 : b ≤ 5 := by
        nlinarith [sq_nonneg (a - 2 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (c - 2 : ℤ), 
            h_eq, h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
      have h13 : c ≤ 5 := by
        nlinarith [sq_nonneg (a - 2 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (c - 2 : ℤ), 
            h_eq, h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
      interval_cases a <;> interval_cases b <;> omega
    · -- Backward
      rintro ⟨r1, r2, r3⟩
      rw [show a = 2 by linarith [r1, r2, r3], 
          show b = 2 by linarith [r1, r2, r3],
          show c = 2 by linarith [r1, r2, r3]
        ]
      all_goals
        norm_num