import Mathlib

theorem algebra_9768 {a b : ℕ → ℝ} (ha : ∃ d, (∀ n, a n = a 0 + d * n) ∧ (0 < d))
    (hb : ∀ n, a n = ∑ i ∈ Finset.Icc 1 n, b i / 2 ^ i)
    (h3 : a 3 * a 6 = 55) (h2 : a 2 + a 7 = 16) :
    (∀ n, a n = 2 * n - 1) ∧
    (∀ n, 1 ≤ n → ∑ i ∈ Finset.Icc 1 n, b i = 2 ^ (n + 2) - 6) := by

  -- hb 0 tells that a 0 = 0
  have h4 : a 0 = 0 := by
    have h0 := hb 0
    norm_num [Finset.sum_eq_zero] at h0 ⊢
    all_goals linarith

  rcases ha with ⟨d, ha1, hd1⟩
  have eq1 : a 2 + a 7 = 16 := h2
  have eq2 : a 3 * a 6 = 55 := h3

  have h2' : a 2 = a 0 + 2 * d := by
    specialize ha1 2
    norm_num at ha1 ⊢
    linarith
  have h7' : a 7 = a 0 + 7 * d := by
    specialize ha1 7
    norm_num at ha1 ⊢
    linarith
  have h3' : a 3 = a 0 + 3 * d := by
    specialize ha1 3
    norm_num at ha1 ⊢
    linarith
  have h6' : a 6 = a 0 + 6 * d := by
    specialize ha1 6
    norm_num at ha1 ⊢
    linarith

  rw [h2', h7'] at eq1
  have h_eq1 : 2 * a 0 + 9 * d = 16 := by linarith

  rw [h3', h6'] at eq2
  have h_eq2 : (a 0 + 3 * d) * (a 0 + 6 * d) = 55 := by
    linarith

  rw [h4] at h_eq1 h_eq2
  norm_num at h_eq1 h_eq2
  nlinarith