import Mathlib



theorem number_theory_608925 (a b c : ℤ) (ha : 0 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9) (hc : 0 ≤ c ∧ c ≤ 9)
  : (792 ∣ 5*10^6 + a*10^5 + b*10^4 + 3700 + c*10 + 2 ) ↔ (a, b, c) ∈ [(0, 5, 5), (4, 5, 1), (6, 4, 9)] := by
  simp
  constructor
  .
    intro h
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    interval_cases a <;> interval_cases b <;> interval_cases c
    <;> norm_num at h ⊢
    <;> tauto
  .
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    all_goals
      norm_num