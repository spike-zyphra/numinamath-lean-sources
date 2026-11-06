import Mathlib

theorem number_theory_53468 {a b n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h1 : a * b = n) (h2 : ∃ k, a = k * n ∧ b = k * n + 98) :
    a = 3 ∧ b = 42 := by
  rcases h2 with ⟨k, h3, h4⟩
  have eq1 : (k * n) * (k * n + 98) = a * b := by 
    rw [show a = k * n by linarith [h3], show b = k * n + 98 by linarith [h4]]
  have eq2 : (k * n) * (k * n + 98) = n := by
    nlinarith [eq1, h1]
  by_cases h : n > 0
  · -- Case n > 0
    have h3g : k ≥ 1 := by
      by_contra h'
      push_neg at h'
      have : k = 0 := by omega
      rw [this] at h3
      nlinarith
    have h4g : k * n > 0 := by
      nlinarith
    nlinarith [sq_nonneg (k * n), sq_nonneg (k * n + 98), sq_pos_of_pos ha, sq_pos_of_pos hb, h3g, sq_nonneg (k * 98), sq_nonneg ((k: ℕ) * (k: ℕ)), h]
  · -- Case n = 0
    have hn0 : n = 0 := by
      omega
    have ha0 : a = 0 := by
      rw [show n = 0 by linarith [hn0]] at h3
      omega
    nlinarith