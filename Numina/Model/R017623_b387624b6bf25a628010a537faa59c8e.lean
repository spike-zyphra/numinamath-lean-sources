import Mathlib


theorem number_theory_6384
(a b c d m : ℕ)
(h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
(h₁ : a + b + c + d = m)
(h₂ : a * b * c * d = m) :
m = 8 := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have h3 : a + b + c + d = a * b * c * d := by
    nlinarith
  have h4 : a ≤ 4 := by
    by_contra h
    push_neg at h
    have h5 : b ≤ 3 := by
      nlinarith [mul_pos hb hc, mul_pos hb (show 0 < d by linarith), mul_pos hc (show 0 < d by linarith),
                mul_pos (show 0 < a by linarith) hb, mul_pos (show 0 < a by linarith) hc, mul_pos (show 0 < a by linarith) (show 0 < d by linarith)]
    have h6 : c ≤ 3 := by
      nlinarith [mul_pos hb hc, mul_pos hb (show 0 < d by linarith), mul_pos hc (show 0 < d by linarith),
                mul_pos (show 0 < a by linarith) hb, mul_pos (show 0 < a by linarith) hc, mul_pos (show 0 < a by linarith) (show 0 < d by linarith)]
    have h7 : d ≤ 3 := by
      nlinarith [mul_pos hb hc, mul_pos hb (show 0 < d by linarith), mul_pos hc (show 0 < d by linarith),
                mul_pos (show 0 < a by linarith) hb, mul_pos (show 0 < a by linarith) hc, mul_pos (show 0 < a by linarith) (show 0 < d by linarith)]
    interval_cases b <;> interval_cases c <;> interval_cases d
    all_goals
      omega
  have h5 : b ≤ 4 := by
    by_contra h
    push_neg at h
    have h6 : a ≤ 3 := by
      nlinarith [mul_pos ha hc, mul_pos ha (show 0 < d by linarith), mul_pos hc (show 0 < d by linarith),
                mul_pos (show 0 < b by linarith) ha, mul_pos (show 0 < b by linarith) hc, mul_pos (show 0 < b by linarith) (show 0 < d by linarith)]
    have h7 : c ≤ 3 := by
      nlinarith [mul_pos ha hc, mul_pos ha (show 0 < d by linarith), mul_pos hc (show 0 < d by linarith),
                mul_pos (show 0 < b by linarith) ha, mul_pos (show 0 < b by linarith) hc, mul_pos (show 0 < b by linarith) (show 0 < d by linarith)]
    have h8 : d ≤ 3 := by
      nlinarith [mul_pos ha hc, mul_pos ha (show 0 < d by linarith), mul_pos hc (show 0 < d by linarith),
                mul_pos (show 0 < b by linarith) ha, mul_pos (show 0 < b by linarith) hc, mul_pos (show 0 < b by linarith) (show 0 < d by linarith)]
    interval_cases a <;> interval_cases c <;> interval_cases d
    all_goals
      omega
  have h6 : c ≤ 4 := by
    by_contra h
    push_neg at h
    have h7 : a ≤ 3 := by
      nlinarith [mul_pos ha hb, mul_pos ha (show 0 < d by linarith), mul_pos hb (show 0 < d by linarith),
                mul_pos (show 0 < c by linarith) ha, mul_pos (show 0 < c by linarith) hb, mul_pos (show 0 < c by linarith) (show 0 < d by linarith)]
    have h8 : b ≤ 3 := by
      nlinarith [mul_pos ha hb, mul_pos ha (show 0 < d by linarith), mul_pos hb (show 0 < d by linarith),
                mul_pos (show 0 < c by linarith) ha, mul_pos (show 0 < c by linarith) hb, mul_pos (show 0 < c by linarith) (show 0 < d by linarith)]
    have h9 : d ≤ 3 := by
      nlinarith [mul_pos ha hb, mul_pos ha (show 0 < d by linarith), mul_pos hb (show 0 < d by linarith),
                mul_pos (show 0 < c by linarith) ha, mul_pos (show 0 < c by linarith) hb, mul_pos (show 0 < c by linarith) (show 0 < d by linarith)]
    interval_cases a <;> interval_cases b <;> interval_cases d
    all_goals
      omega
  have h7 : d ≤ 4 := by
    by_contra h
    push_neg at h
    have h8 : a ≤ 3 := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
                mul_pos (show 0 < d by linarith) ha, mul_pos (show 0 < d by linarith) hb, mul_pos (show 0 < d by linarith) hc]
    have h9 : b ≤ 3 := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
                mul_pos (show 0 < d by linarith) ha, mul_pos (show 0 < d by linarith) hb, mul_pos (show 0 < d by linarith) hc]
    have h10 : c ≤ 3 := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
                mul_pos (show 0 < d by linarith) ha, mul_pos (show 0 < d by linarith) hb, mul_pos (show 0 < d by linarith) hc]
    interval_cases a <;> interval_cases b <;> interval_cases c
    all_goals
      omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d
  all_goals
    omega