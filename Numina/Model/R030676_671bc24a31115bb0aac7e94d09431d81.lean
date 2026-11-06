import Mathlib

theorem inequalities_611159 :
    IsLeast {k : ℝ | ∃ r s : ℤ, 3 * r ≥ 2 * s - 3 ∧ 4 * s ≥ r + 12 ∧ k = r / s} (1 / 2) := by
  constructor
  · -- Show that 1/2 is in the set
    use 2, 4
    norm_num
  · -- Show that 1/2 is indeed the smallest
    intro k hk
    rcases hk with ⟨r, s, h1, h2, hk⟩
    by_contra h
    push_neg at h
    have h3 : (r : ℝ) / (s : ℝ) < (1 / 2 : ℝ) := by linarith [hk, h]
    have h4 : s > 0 := by
      by_contra h5
      push_neg at h5
      have h5' : s ≤ 0 := by omega
      have h6 : r ≤ -12 := by
        nlinarith [h2, h5']
      have h7 : s ≤ -17 := by
        nlinarith [h1, h6]
      nlinarith
    have h9 : 2 * r < s := by
      have h10 : (r : ℝ) / (s : ℝ) < (1 / 2 : ℝ) := h3
      have h11 : s > 0 := by exact_mod_cast h4
      have h12 : (r : ℝ) < (1 / 2 : ℝ) * (s : ℝ) := by
        have h12 : (r : ℝ) / (s : ℝ) < (1 / 2 : ℝ) := h3
        apply (div_lt_iff₀ (by exact_mod_cast h4)).mp at h12
        linarith
      have h13 : 2 * (r : ℝ) < (s : ℝ) := by
        linarith
      exact_mod_cast h13
    have h10 : r < 3 := by
      nlinarith [h1, h9]
    have h11 : r ≤ 2 := by omega
    have h12 : s ≥ 4 := by
      nlinarith [h2, h11]
    have h13 : s ≥ 5 := by
      omega
    nlinarith