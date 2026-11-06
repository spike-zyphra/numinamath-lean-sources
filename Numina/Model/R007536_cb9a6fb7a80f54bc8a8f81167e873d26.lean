import Mathlib

theorem number_theory_15761 : (0 ≤ n ∧ n ≤ 5 ∧ n ≡ -3736 [ZMOD 6]) → n = 2 := by
  intro h
  rcases h with ⟨h0, h1, h2⟩
  norm_num [Int.ModEq] at h2 
  omega