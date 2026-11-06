import Mathlib

theorem number_theory_610639 (a b c d : ℕ) (hpos : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (hdig : a < 10 ∧ b < 10 ∧ c < 10 ∧ d < 10)
    (hmul : 5.6 = (Nat.ofDigits 10 [a, b] : ℚ) / 10 * ((Nat.ofDigits 10 [c, d] : ℚ) / 10)) :
    (Nat.ofDigits 10 [a, b] : ℚ) / 10 + (Nat.ofDigits 10 [c, d] : ℚ) / 10 = 5.1 := by
      -- Nat.ofDigits 10 [a, b] = 10 * a + b，Nat.ofDigits 10 [c, d] = 10 * c + d
      simp [Nat.ofDigits, List.foldl] at hmul ⊢
      norm_num at hmul ⊢
      rcases hpos with ⟨ha1, hb1, hc1, hd1⟩
      rcases hdig with ⟨ha2, hb2, hc2, hd2⟩
      interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;> norm_num at hmul ⊢ <;> tauto