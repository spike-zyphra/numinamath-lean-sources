import Mathlib

theorem algebra_11975 (n : ℕ) (h : n > 0) (a : ℝ) (ha : a = 1 / 4) (h' : ∑ i ∈ Finset.range n, a * (1 / 2)^i = 63 / 128) :
    n = 6 := by 
  rw [ha] at h'
  have h1 : ∀ n : ℕ, ∑ i in Finset.range n, (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ i = (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ) ^ n) := by
    intro n 
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp at *
      ring
  have h2 : (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ) ^ n) = (63 / 128 : ℝ) := by
    have hn := h1 n 
    rw [hn] at h'
    all_goals linarith
  have h3 : (1 - (1 / 2 : ℝ) ^ n) = (63 / 64 : ℝ) := by
    linarith
  have h4 : (1 / 2 : ℝ) ^ n = (1 / 64 : ℝ) := by
    linarith
  have h5 : (1 / 2 : ℝ) ^ n = (1 / 2 : ℝ) ^ (6 : ℕ) := by
    rw [h4]
    norm_num
  have h6 : n = (6 : ℕ) := by
    have h7 : (1 / 2 : ℝ) ^ n = (1 / 2 : ℝ) ^ (6 : ℕ) := h5
    have h8 : n = (6 : ℕ) := by
      exact Nat.cast_injective ((by simpa using h7 : (n : ℕ) = (6 : ℕ)))
    exact h8
  exact h6