import Mathlib

theorem inequalities_196859 (a : ℕ → ℕ) (ha : a 0 < a 1 ∧ a 1 < a 2 ∧ a 2 < a 3 ∧ a 3 < a 4 ∧ a 4 < a 5 ∧ a 5 < a 6 ∧ a 6 < a 7 ∧ a 7 < a 8 ∧ a 8 < a 9)
    (h : a 0 ≥ (1 / 2 : ℚ) * a 9) (h' : ∑ i ∈ Finset.range 10, a i = 150) :
    a 5 = 16 := by
  have h1 : a 0 < a 1 := by linarith [ha.1]
  have h2 : a 1 < a 2 := by linarith [ha.2.1]
  have h3 : a 2 < a 3 := by linarith [ha.2.2.1]
  have h4 : a 3 < a 4 := by linarith [ha.2.2.2.1]
  have h5 : a 4 < a 5 := by linarith [ha.2.2.2.2.1]
  have h6 : a 5 < a 6 := by linarith [ha.2.2.2.2.2.1]
  have h7 : a 6 < a 7 := by linarith [ha.2.2.2.2.2.2.1]
  have h8 : a 7 < a 8 := by linarith [ha.2.2.2.2.2.2.2.1]
  have h9 : a 8 < a 9 := by linarith [ha.2.2.2.2.2.2.2.2]
  have h10 : (a 0 : ℚ) ≥ (1 / 2 : ℚ) * (a 9 : ℚ) := by exact_mod_cast h
  have h11 : 2 * (a 0 : ℚ) ≥ (a 9 : ℚ) := by linarith
  have h12 : 2 * a 0 ≥ a 9 := by exact_mod_cast h11
  have h13 : a 9 ≥ a 8 + 1 := by omega
  have h14 : a 8 ≥ a 7 + 1 := by omega
  have h15 : a 7 ≥ a 6 + 1 := by omega
  have h16 : a 6 ≥ a 5 + 1 := by omega
  have h17 : a 5 ≥ a 4 + 1 := by omega
  have h18 : a 4 ≥ a 3 + 1 := by omega
  have h19 : a 3 ≥ a 2 + 1 := by omega
  have h20 : a 2 ≥ a 1 + 1 := by omega
  have h21 : a 1 ≥ a 0 + 1 := by omega
  norm_num [Finset.sum_range_succ] at h'
  omega