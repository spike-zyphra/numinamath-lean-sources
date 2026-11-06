import Mathlib

theorem algebra_159953 (x y z : ℝ) (h₀ : x + y + Real.sin z ^ 2 = 12) (h₁ : x * y = 36) :
    x = 6 ∧ y = 6 ∧ ∃ k : ℤ, z = k * Real.pi := by
  have h2 : Real.sin z ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h3 : Real.sin z ^ 2 ≤ 1 := by
    apply Real.sin_sq_le_one
  have h4 : x + y ≤ 12 := by
    nlinarith [h₀, h2]
  have h5 : x + y ≥ 11 := by
    nlinarith [h₀, h3]
  have h6 : (x + y) ^ 2 ≥ 144 := by
    nlinarith [sq_nonneg (x - y), h₁]
  have h7 : x + y = 12 := by
    nlinarith
  have h8 : Real.sin z ^ 2 = 0 := by
    nlinarith [h₀, h7]
  have h9 : Real.sin z = 0 := by
    nlinarith
  have h10 : ∃ k : ℤ, z = k * Real.pi := by 
    rw [Real.sin_eq_zero_iff] at h9
    rcases h9 with ⟨k, hk⟩
    refine ⟨k, by linarith⟩
  have h11 : x = 6 := by
    nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6), h7, h₁]
  have h12 : y = 6 := by
    nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 6), h7, h₁]
  exact ⟨h11, h12, h10⟩