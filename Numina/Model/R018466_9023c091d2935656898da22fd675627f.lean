import Mathlib

theorem algebra_300064 (a : ℝ) (ha : a > 2) (a_seq : ℕ → ℝ)
    (h_a0 : a_seq 0 = 1) (h_a1 : a_seq 1 = a)
    (h_an : ∀ n, a_seq (n + 1) = ((a_seq n)^2 / (a_seq (n - 1))^2 - 2) * a_seq n) :
    ∀ k, ∑ i in Finset.range (k + 1), (1 / a_seq i) < ((1 / 2) * (2 + a - Real.sqrt (a^2 - 4))) := by 
  have h1 := h_an 0
  have eq1 : a_seq (0 - 1) = a_seq 0 := by
    simp
  simp [h_a0, h_a1, eq1] at h1 
  linarith