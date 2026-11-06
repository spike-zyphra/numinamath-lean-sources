import Mathlib

theorem algebra_171027 :
    IsLeast {x | ∃ a b c d e : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ e > 0 ∧ a + b + c + d + e = 2345 ∧ x = max (max (max (a + b) (b + c)) (c + d)) (d + e)} 782 := by
  constructor
  · -- First part, showing 782 is achievable
    use 781, 1, 781, 1, 781
    all_goals norm_num
  · -- Second part, showing no value less than 782 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, e, ha, hb, hc, hd, he, hsum, hmax⟩
    by_contra h
    push_neg at h
    -- Unfold the max expressions to derive contradiction
    have h1 : max (max (max (a + b) (b + c)) (c + d)) (d + e) < 782 := by
      omega
    have h2 : a + b < 782 := by
      have h2_a1 : a + b ≤ max (max (max (a + b) (b + c)) (c + d)) (d + e) := by
        simp
      have h2_a2 : max (max (max (a + b) (b + c)) (c + d)) (d + e) < 782 := by
        linarith [h1]
      linarith
    have h3 : b + c < 782 := by
      have h3_a1 : b + c ≤ max (max (max (a + b) (b + c)) (c + d)) (d + e) := by
        simp
      have h3_a2 : max (max (max (a + b) (b + c)) (c + d)) (d + e) < 782 := by
        linarith [h1]
      linarith
    have h4 : c + d < 782 := by
      have h4_a1 : c + d ≤ max (max (max (a + b) (b + c)) (c + d)) (d + e) := by
        simp
      have h4_a2 : max (max (max (a + b) (b + c)) (c + d)) (d + e) < 782 := by
        linarith [h1]
      linarith
    have h5 : d + e < 782 := by
      have h5_a1 : d + e ≤ max (max (max (a + b) (b + c)) (c + d)) (d + e) := by
        simp
      have h5_a2 : max (max (max (a + b) (b + c)) (c + d)) (d + e) < 782 := by
        linarith [h1]
      linarith
    -- Total of the four pairs
    have h6 : a + 2 * b + 2 * c + 2 * d + e < 4 * 782 := by
      omega
    -- The sum of all variables
    have h7 : a + b + c + d + e = 2345 := hsum
    -- Derive contradiction with the total sum constraint
    omega