import Mathlib

theorem number_theory_134947 (a b c : ℕ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h : a ∈ Finset.Icc 1 9) (h' : b ∈ Finset.Icc 1 9) (h'' : c ∈ Finset.Icc 1 9)
    (h''' : 100 * a + 10 * b + c + 100 * c + 10 * b + a = 545) :
    a + b + c = 7 := by 
  simp at h h' h''
  rcases h with ⟨ha1, ha2⟩
  rcases h' with ⟨hb1, hb2⟩
  rcases h'' with ⟨hc1, hc2⟩
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega
  all_goals omega