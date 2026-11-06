import Mathlib

theorem inequalities_616699 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 + a + b + c = 2 * a * b * c) :
    3 / 2 ≤ a * b / (1 + a + b : ℚ) + b * c / (1 + b + c : ℚ) +
    c * a / (1 + c + a : ℚ) := by
  have h1 : a ≤ 3 := by
    nlinarith [show 0 < b by linarith, show 0 < c by linarith, 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h2 : b ≤ 3 := by
    nlinarith [show 0 < a by linarith, show 0 < c by linarith, 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h3 : c ≤ 3 := by
    nlinarith [show 0 < a by linarith, show 0 < b by linarith, 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  interval_cases a <;> interval_cases b <;> interval_cases c 
    <;> norm_num at h ⊢
    <;> omega