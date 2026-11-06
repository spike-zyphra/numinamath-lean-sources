import Mathlib

/- Show that the square of every odd integer is of the form \(8k + 1\).-/
theorem number_theory_4976
    (n : ℤ)
    (h : Odd n) :
    ∃ k, n^2 = 8 * k + 1 := by
  -- n = 2 * m + 1
  obtain ⟨m, hm⟩ := h
  -- n * (n + 1) = k + k
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self m
  use k
  calc n ^ 2
    _ = 4 * m * (m + 1) + 1 := by rw [hm]; ring
    _ = 8 * k + 1 := by rw [mul_assoc, hk]; ring
