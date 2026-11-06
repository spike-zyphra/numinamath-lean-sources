import Mathlib

theorem algebra_244433 (a b c d e : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hd : d > 0) (he : e > 0) (hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
    c ≠ d ∧ c ≠ e ∧ d ≠ e) (hsum : a + b + c + d + e = 55) :
    max a (max b (max c (max d e))) ≤ 45 := by
  have h1 : a > 0 := by omega
  have h2 : b > 0 := by omega
  have h3 : c > 0 := by omega
  have h4 : d > 0 := by omega
  have h5 : e > 0 := by omega
  have h9 : a ≤ 45 := by
    by_contra h
    push_neg at h
    have h10 : a ≥ 46 := by omega
    have h11 : b + c + d + e ≤ 9 := by
      omega
    omega
  have h10 : b ≤ 45 := by
    by_contra h
    push_neg at h
    have h11 : b ≥ 46 := by omega
    have h12 : a + c + d + e ≤ 9 := by
      omega
    omega
  have h11 : c ≤ 45 := by
    by_contra h
    push_neg at h
    have h12 : c ≥ 46 := by omega
    have h13 : a + b + d + e ≤ 9 := by
      omega
    omega
  have h12 : d ≤ 45 := by
    by_contra h
    push_neg at h
    have h13 : d ≥ 46 := by omega
    have h14 : a + b + c + e ≤ 9 := by
      omega
    omega
  have h13 : e ≤ 45 := by
    by_contra h
    push_neg at h
    have h14 : e ≥ 46 := by omega
    have h15 : a + b + c + d ≤ 9 := by
      omega
    omega
  have h14 : max a (max b (max c (max d e))) ≤ 45 := by
    have h9' : a ≤ 45 := h9
    have h10' : b ≤ 45 := h10
    have h11' : c ≤ 45 := h11
    have h12' : d ≤ 45 := h12
    have h13' : e ≤ 45 := h13
    simp [max_le_iff]
    all_goals omega
  linarith