import Mathlib

theorem number_theory_198406 (n : ℕ) (hn : Odd n ∧ n ≥ 3) :
    ∃ k, (∑ i in Finset.Icc 1 (n - 1), (1 : ℚ) / i) * 2 * 3 * 4 * ∏ i ∈ Finset.Icc 1 (n - 1), i = k * n := by
  have h1 : (n : ℚ) ≠ 0 := by
    have hn3 : n ≥ 3 := hn.right
    have hn4 : n ≥ 3 := hn3
    have hn5 : (n : ℚ) ≥ (3 : ℚ) := by exact_mod_cast hn4
    nlinarith
  use (∑ i in Finset.Icc 1 (n - 1), (1 : ℚ) / i) * (∏ i ∈ Finset.Icc 1 (n - 1), (i : ℚ)) * (24 / (n : ℚ))
  field_simp [h1]
  <;> try { ring }
  <;> try { tauto }
  all_goals try { norm_num }
  <;> try { nlinarith }