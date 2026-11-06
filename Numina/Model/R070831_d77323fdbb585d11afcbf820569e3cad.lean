import Mathlib

theorem algebra_94448 {a b : ℕ → ℕ} (ha : ∀ n, a n ≤ a (n + 1)) (hb : ∀ n, b n ≤ b (n + 1))
    (h1 : a 0 ≠ b 0) (h2 : ∀ n, a (n + 2) = a n + a (n + 1)) (h3 : ∀ n, b (n + 2) = b n + b (n + 1))
    (h4 : a 6 = N) (h5 : b 6 = N) :
    N ≥ 104 := by
  have a1 : a 1 ≥ a 0 := ha 0
  have a2 : a 2 = a 0 + a 1 := h2 0
  have a3 : a 3 = a 1 + a 2 := by
    specialize h2 1
    simpa using h2
  have a4 : a 4 = a 2 + a 3 := by
    specialize h2 2
    simpa using h2
  have a5 : a 5 = a 3 + a 4 := by
    specialize h2 3
    simpa using h2
  have a6 : a 6 = a 4 + a 5 := by
    specialize h2 4
    simpa using h2
  have b1 : b 1 ≥ b 0 := hb 0
  have b2 : b 2 = b 0 + b 1 := h3 0
  have b3 : b 3 = b 1 + b 2 := by
    specialize h3 1
    simpa using h3
  have b4 : b 4 = b 2 + b 3 := by
    specialize h3 2
    simpa using h3
  have b5 : b 5 = b 3 + b 4 := by
    specialize h3 3
    simpa using h3
  have b6 : b 6 = b 4 + b 5 := by
    specialize h3 4
    simpa using h3
  rw [a6] at h4
  rw [a5] at h4
  rw [a4] at h4
  rw [a3] at h4
  rw [a2] at h4
  rw [b6] at h5
  rw [b5] at h5
  rw [b4] at h5
  rw [b3] at h5
  rw [b2] at h5
  omega