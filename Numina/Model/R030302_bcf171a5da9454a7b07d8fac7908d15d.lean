import Mathlib

theorem number_theory_238876 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hord : a < b ∧ b < c) (h : a * b + b * c + c * a = a * b * c) :
    a = 2 ∧ b = 3 ∧ c = 6 := by
  have h1 : a < b := hord.1
  have h2 : b < c := hord.2
  have h3 : a = 2 := by
    nlinarith [h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
      mul_pos (show 0 < a by linarith) (show 0 < c by linarith),
      mul_pos (show 0 < b by linarith) (show 0 < c by linarith)
    ]
  have h4 : b = 3 := by
    rw [h3] at h
    nlinarith [h, mul_pos (show 0 < (2 : ℕ) by norm_num) hb, mul_pos (show 0 < (2 : ℕ) by norm_num) hc, 
      mul_pos hb hc
    ]
  have h5 : c = 6 := by
    rw [h3, h4] at h
    nlinarith
  exact ⟨h3, h4, h5⟩