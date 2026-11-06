import Mathlib

theorem number_theory_262772 (n : ℕ) (h : n > 0) (h1 : (n + 1)^2 = n^2 + 146 + 31) :
    (n + 1)^2 = 7921 := by
  have eqn1 : (n + 1)^2 = n^2 + 2 * n + 1 := by
    ring
  rw [eqn1] at h1
  have h2 : 2 * n + 1 = 177 := by
    omega
  have hn : n = 88 := by
    omega
  calc
    (n + 1)^2 = (88 + 1)^2 := by rw [hn]
    _ = 89^2 := by norm_num
    _ = 7921 := by norm_num