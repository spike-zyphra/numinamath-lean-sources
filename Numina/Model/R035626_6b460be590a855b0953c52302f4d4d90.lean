import Mathlib

theorem number_theory_296488 :
    ¬∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧ a + b + c = 6 ∧ ∃ k : ℤ, k = (1/2) * a * b := by
  rintro ⟨a, b, c, ha, hb, hc, h1, h2, ⟨k, hk⟩⟩
  have h3 : a ≤ 4 := by
    omega
  have h4 : b ≤ 4 := by
    omega
  have h5 : c ≤ 4 := by
    omega
  interval_cases a <;> interval_cases b <;> interval_cases c
  all_goals
    norm_num at h1 h2 hk
    all_goals
      omega