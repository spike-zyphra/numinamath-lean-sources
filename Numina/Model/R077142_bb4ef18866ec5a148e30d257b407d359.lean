import Mathlib

theorem number_theory_236448 (x : ℕ) (h : x > 0) (h1 : ∃ n, x + 13 = n * (x - 37)) :
    x ≤ 87 := by
  rcases h1 with ⟨n, hn⟩
  by_contra h2
  push_neg at h2
  have h3 : x ≥ 38 := by
    omega
  have h4 : n ≥ 2 := by
    by_contra h5
    push_neg at h5
    have h6 : n = 0 ∨ n = 1 := by
      omega
    rcases h6 with (h7 | h8)
    · -- If n = 0 then x + 13 = 0, which is false since x > 0
      rw [h7] at hn
      omega
    · -- If n = 1 then x + 13 = x - 37
      rw [h8] at hn
      omega
  have eq1 : x + 13 = n * (x - 37) := hn
  have h8 : n ≤ 51 := by
    by_contra h9
    push_neg at h9
    have h9' : n ≥ 52 := by omega
    have h10 : x + 13 ≥ 52 * (x - 37) := by
      have h11 : n * (x - 37) = x + 13 := by
        linarith [eq1]
      have h12 : n ≥ 52 := h9'
      have h13 : n * (x - 37) ≥ 52 * (x - 37) := by
        have h14 : x - 37 > 0 := by omega
        nlinarith
      linarith [h11, h13]
    have h11 : x ≤ 38 := by
      omega
    omega
  interval_cases n <;> omega