import Mathlib

theorem number_theory_279436 (a b c d : ℕ) (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (hg : a > 0) (hg' : b > 0) (hg'' : c > 0)
    (hg''' : d > 0) (h : a + b + c + d = 20) :
    max (max a b) (max c d) ≤ 14 := by
  have h1 : a ≤ 14 := by
    by_contra h1
    push_neg at h1
    have h2 : b + c + d ≤ 5 := by linarith
    have h3 : b ≥ 1 := by linarith
    have h4 : c ≥ 1 := by linarith
    have h5 : d ≥ 1 := by linarith
    have h6 : b < c := by
      omega
    have h7 : b ≠ c := by
      exact hd
    omega
  have h2 : b ≤ 14 := by
    by_contra h2
    push_neg at h2
    have h6 : a + c + d ≤ 5 := by linarith
    have h7 : a ≥ 1 := by linarith
    have h8 : c ≥ 1 := by linarith
    have h9 : d ≥ 1 := by linarith
    omega
  have h3 : c ≤ 14 := by
    by_contra h3
    push_neg at h3
    have h4 : a + b + d ≤ 5 := by linarith
    have h5 : a ≥ 1 := by linarith
    have h6 : b ≥ 1 := by linarith
    have h7 : d ≥ 1 := by linarith
    omega
  have h4 : d ≤ 14 := by
    by_contra h4
    push_neg at h4
    have h5 : a + b + c ≤ 5 := by linarith
    have h6 : a ≥ 1 := by linarith
    have h7 : b ≥ 1 := by linarith
    have h8 : c ≥ 1 := by linarith
    omega
  have h5 : max (max a b) (max c d) ≤ 14 := by
    have h7 : a ≤ 14 := h1
    have h8 : b ≤ 14 := h2
    have h9 : c ≤ 14 := h3
    have h10 : d ≤ 14 := h4
    simp [max_le_iff, h7, h8, h9, h10]
    all_goals omega
  exact h5