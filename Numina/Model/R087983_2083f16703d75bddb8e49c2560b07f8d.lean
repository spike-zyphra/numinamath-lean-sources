import Mathlib

theorem algebra_282659 {n : ℕ} (hn : n ≠ 0) (h : (2 / 5 : ℝ) * n * 220 + (2 / 5 : ℝ) * n * 200 + 150 * 180 = (3 / 5 : ℝ) * n * 220 + (3 / 5 : ℝ) * n * 200 + 150 * 180 + 4320) :
    n = 360 := by
  have h1 : (n : ℝ) > 0 := by
    have hn' : (n : ℝ) > 0 := by
      have hne : (n : ℝ) ≠ 0 := by
        exact_mod_cast hn
      by_contra h'
      push_neg at h'
      have : (n : ℝ) = 0 := by linarith
      contradiction
    linarith
  have h2 : (n : ℝ) = 0 := by
    ring_nf at h
    linarith
  have h3 : (n : ℝ) > 0 := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  linarith