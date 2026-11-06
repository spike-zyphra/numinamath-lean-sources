import Mathlib

theorem algebra_267647 :
    {(x, y) : ℤ × ℤ | x * y + x + y = 34 ∧ x ^ 2 + y ^ 2 - x - y = 42} =
    {(4, 6), (6, 4)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) is in the left side set
    rintro ⟨h1, h2⟩
    have h3 : (x + y) ^ 2 + (x + y) - 110 = 0 := by
      nlinarith [h1, h2]
    have h3' : (x + y - 10) * (x + y + 11) = 0 := by
      ring_nf at h3 ⊢
      linarith
    cases' (mul_eq_zero.mp h3') with h4 h5
    · -- Case x + y = 10
      have h6 : x + y = 10 := by linarith
      have h7 : x * y = 24 := by
        nlinarith [h1, h6]
      have h10 : x = 4 ∨ x = 6 := by
        have h8 : x ≤ 10 := by nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 10), sq_nonneg (x * y - 24)]
        have h9 : x ≥ 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 10), sq_nonneg (x * y - 24)]
        interval_cases x <;> omega
      cases' h10 with hx4 hx6
      · -- Case x = 4
        have hy6 : y = 6 := by linarith
        simp [hx4, hy6]
      · -- Case x = 6
        have hy4 : y = 4 := by linarith
        simp [hx6, hy4]
    · -- Case x + y = -11
      have h8 : x + y = -11 := by linarith
      have h9 : x * y = 45 := by
        nlinarith [h1, h8]
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 45)]
  · -- Show the two pairs (4,6) and (6,4) are in the set.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (4, 6)
      constructor <;> norm_num
    · -- Check (6, 4)
      constructor <;> norm_num