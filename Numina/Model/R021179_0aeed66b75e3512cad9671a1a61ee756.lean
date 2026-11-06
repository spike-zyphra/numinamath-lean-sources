import Mathlib

theorem algebra_262613 {b c : ℤ} (h : ∀ x : ℤ, x^2 + b * x + c > 0) : b^2 - 4 * c ≤ 0 := by
  by_contra h1
  push_neg at h1
  have h2 : b ^ 2 - 4 * c ≥ 1 := by
    omega
  by_cases h3 : b % 2 = 0 
  · -- Assume $b$ is even, so $b = 2k$ for some integer $k$
    have h5 : ∃ k : ℤ, b = 2 * k := by 
      use b / 2 
      omega 
    rcases h5 with ⟨k, hk⟩ 
    have h5 : c > k ^ 2 := by 
      have hk1 : (-k) ^ 2 + b * (-k) + c > 0 := h (-k)
      simp [show b = 2 * k by linarith [hk]] at hk1 ⊢ 
      nlinarith 
    have h6 : b ^ 2 - 4 * c < 0 := by
      rw [show b = 2 * k by linarith [hk]]
      nlinarith
    linarith 
  · -- Assume $b$ is odd, so $b = 2k + 1$ for some integer $k$
    have h10 : b % 2 = 1 := by 
      omega 
    have h11 : ∃ k : ℤ, b = 2 * k + 1 := by 
      have : b % 2 = 1 := h10 
      have h3 : b = 2 * (b / 2) + 1 := by omega 
      use b / 2 
      all_goals omega 
    rcases h11 with ⟨k, hk⟩ 
    have h8 := h (-k - 1)
    rw [show b = 2 * k + 1 by linarith [hk]] at h8
    have h9 : c > k * (k + 1) := by 
      nlinarith
    have h10 : b ^ 2 - 4 * c < 0 := by
      rw [show b = 2 * k + 1 by linarith [hk]]
      nlinarith
    linarith