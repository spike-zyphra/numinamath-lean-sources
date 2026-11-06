import Mathlib

theorem algebra_6550 :
  IsLeast {z : ℕ | ∃ x y : ℤ, x > 0 ∧ y > 0 ∧ 7 * x - 2 * y = 151 ∧ z = |x - y|} 2 := by
  constructor
  · -- First, show that 2 belongs to the set.
    use 31, 33
    norm_num
  · -- Now, show that any element in the set is ≥ 2.
    intro z h
    rcases h with ⟨x, y, hx1, hy1, h1, h2⟩
    by_contra h3
    push_neg at h3
    have h3' : z < 2 := by linarith
    have h4 : z = 0 ∨ z = 1 := by
      have : z < 2 := h3'
      omega
    rcases h4 with (h4 | h4)
    · -- Assume z = 0, which implies |x - y| = 0.
      have h5 : |x - y| = 0 := by
        omega
      have h8 : x - y = 0 := by
        simpa [abs_eq_zero] using h5
      have h9 : x = y := by
        linarith
      have h10 : 5 * x = 151 := by
        have h11 : y = x := by
          linarith [h9]
        rw [h11] at h1
        linarith
      omega
    · -- Assume z = 1, which implies |x - y| = 1.
      have h5 : |x - y| = 1 := by
        omega
      cases' eq_or_eq_neg_of_abs_eq h5 with h6 h7
      · -- Case x - y = 1
        have h8 : x = y + 1 := by linarith
        rw [h8] at h1
        have h9 : 5 * y = 144 := by
          linarith
        omega
      · -- Case x - y = -1
        have h8 : y = x + 1 := by linarith
        rw [h8] at h1
        have h9 : 5 * x = 153 := by
          linarith
        omega