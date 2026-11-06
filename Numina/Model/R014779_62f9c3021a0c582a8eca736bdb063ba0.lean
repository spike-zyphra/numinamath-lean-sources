import Mathlib

theorem number_theory_145290 (a b : ℕ) (ha : 0 < a ∧ a ≤ 12) (hb : 0 < b ∧ b ≤ 12)
    (h : ∃ C, ∀ n, 0 < n → (a ^ n + b ^ (n + 9)) % 13 = C) :
    (a, b) = (1, 1) ∨ (a, b) = (4, 4) ∨ (a, b) = (10, 10) ∨ (a, b) = (12, 12) := by
  rcases h with ⟨C, hC⟩
  have h1 := hC 1 (by norm_num)
  have h2 := hC 2 (by norm_num)
  have h3 := hC 3 (by norm_num)
  have h4 := hC 4 (by norm_num)
  have h5 := hC 5 (by norm_num)
  have h6 := hC 6 (by norm_num)
  have h7 := hC 7 (by norm_num)
  have h8 := hC 8 (by norm_num)
  have h9 := hC 9 (by norm_num)
  have h10 := hC 10 (by norm_num)
  have h11 := hC 11 (by norm_num)
  have h12 := hC 12 (by norm_num)
  have h_a1 : a ≤ 12 := by
    exact ha.2
  have h_a2 : 0 < a := by
    exact ha.1
  have h_b1 : b ≤ 12 := by
    exact hb.2
  have h_b2 : 0 < b := by
    exact hb.1
  interval_cases a <;> interval_cases b <;> norm_num [Prod.ext_iff] at *
  <;> omega