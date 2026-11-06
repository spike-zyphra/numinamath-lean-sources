import Mathlib

theorem number_theory_605469 (m n : ℤ) (hm : 0 < m) (hn : 0 < n)
    (h : 5 * m + n ∣ 5 * n + m) : m ∣ n := by 
  rcases h with ⟨k, hk⟩
  have h1 : 5 * n + m = k * (5 * m + n) := by
    linarith
  have h2 : k > 0 := by
    nlinarith [show 0 < 5 * n + m from by nlinarith, show 0 < 5 * m + n from by nlinarith]
  have h3 : k < 5 := by
    by_contra h'
    push_neg at h'
    have h4 : k ≥ 5 := by nlinarith
    nlinarith [show 0 < m by linarith, show 0 < n by linarith]
  have h4 : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    omega
  rcases h4 with (r | r | r | r)
  · -- Let k = 1
    rw [show k = 1 by omega] at h1
    have eq1 : 5 * n + m = 1 * (5 * m + n) := h1
    have eq2 : n = m := by
      nlinarith
    use 1
    all_goals linarith
  · -- Let k = 2
    rw [show k = 2 by omega] at h1
    have eq1 : 5 * n + m = 2 * (5 * m + n) := h1
    have eq2 : n = 3 * m := by
      nlinarith
    use 3
    all_goals linarith
  · -- Let k = 3
    rw [show k = 3 by omega] at h1
    have eq1 : 5 * n + m = 3 * (5 * m + n) := h1
    have eq2 : n = 7 * m := by
      nlinarith
    use 7
    all_goals linarith
  · -- Let k = 4
    rw [show k = 4 by omega] at h1
    have eq1 : 5 * n + m = 4 * (5 * m + n) := h1
    have eq2 : n = 19 * m := by
      nlinarith
    use 19
    all_goals linarith