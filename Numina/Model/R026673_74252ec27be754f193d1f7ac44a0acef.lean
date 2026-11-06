import Mathlib

theorem number_theory_170206 (m n : ℤ) (_ : 0 < m) (h₀ : 0 < n)
    (h₁ : (5 * m + n) ∣ (5 * n + m)) : m ∣ n := by
  rcases h₁ with ⟨k, hk⟩
  have h2 : 5 * n + m = k * (5 * m + n) := by
    linarith [hk]
  have h3 : k > 0 := by
    nlinarith [show 0 < m by assumption, show 0 < n by assumption, 
      show 0 < 5 * m + n by nlinarith]
  have h4 : k < 5 := by
    by_contra h5
    push_neg at h5
    have h6 : k ≥ 5 := by omega
    nlinarith [show 0 < m by assumption, show 0 < n by assumption, 
      show 0 < 5 * m + n by nlinarith]
  have h5 : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    omega
  rcases h5 with (r | r | r | r)
  · -- Case k = 1
    rw [show k = 1 by linarith [r]] at h2
    have h3 : 5 * n + m = 5 * m + n := by
      linarith [h2]
    have h4 : n = m := by
      linarith [h3]
    use 1
    all_goals
      linarith [h4]
  · -- Case k = 2
    rw [show k = 2 by linarith [r]] at h2
    have h6 : 5 * n + m = 2 * (5 * m + n) := by
      linarith [h2]
    have h7 : n = 3 * m := by
      nlinarith [h6]
    use 3
    all_goals
      linarith [h7]
  · -- Case k = 3
    rw [show k = 3 by linarith [r]] at h2
    have h9 : 5 * n + m = 3 * (5 * m + n) := by
      linarith [h2]
    have h7 : n = 7 * m := by
      nlinarith [h9]
    use 7
    all_goals
      linarith [h7]
  · -- Case k = 4
    rw [show k = 4 by linarith [r]] at h2
    have h12 : 5 * n + m = 4 * (5 * m + n) := by
      linarith [h2]
    have h13 : n = 19 * m := by
      nlinarith [h12]
    use 19
    all_goals
      linarith [h13]