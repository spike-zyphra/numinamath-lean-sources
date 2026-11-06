import Mathlib

theorem number_theory_90347 (m n : ℤ) (hm : 0 < m) (hn : 0 < n)
    (h : 5 * m + n ∣ 5 * n + m) : m ∣ n := by
  rcases h with ⟨k, h1⟩
  have h4 : k > 0 := by
    nlinarith 
  have h5 : k < 5 := by
    by_contra h'
    push_neg at h'
    have h6 : k ≥ 5 := by 
      omega 
    nlinarith 
  have h5' : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    omega
  rcases h5' with (r | r | r | r)
  · -- Case k=1, then n = m.
    have hk1 : k = 1 := r 
    rw [hk1] at h1 
    have h2 : n = m := by 
      nlinarith
    have h3 : m ∣ n := by 
      rw [show n = m by linarith] 
      all_goals 
      use 1 
      all_goals 
      ring 
    exact h3 
  · -- Case k=2, then n = 3m.
    have hk1 : k = 2 := r 
    rw [hk1] at h1 
    have h3 : n = 3 * m := by 
      nlinarith 
    have h4 : m ∣ n := by 
      rw [show n = 3 * m by linarith] 
      all_goals 
      use 3 
      all_goals 
      ring 
    exact h4 
  · -- Case k=3, then n = 7m.
    have hk1 : k = 3 := r 
    rw [hk1] at h1 
    have h3 : n = 7 * m := by 
      nlinarith 
    have h4 : m ∣ n := by 
      rw [show n = 7 * m by linarith] 
      all_goals 
      use 7 
      all_goals 
      ring 
    exact h4 
  · -- Case k=4, then n = 19m.
    have hk1 : k = 4 := r 
    rw [hk1] at h1 
    have h3 : n = 19 * m := by 
      nlinarith 
    have h4 : m ∣ n := by 
      rw [show n = 19 * m by linarith] 
      all_goals 
      use 19 
      all_goals 
      ring 
    exact h4