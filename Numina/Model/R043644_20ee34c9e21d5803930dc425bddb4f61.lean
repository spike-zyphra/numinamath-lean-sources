import Mathlib

theorem number_theory_229850 (n : ℕ) (hn : n > 0) (h2 : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n)
    (h : ∀ a b : ℕ, |(2 ^ a : ℤ) - 3 ^ b| ≠ n) :
    n ≥ 35 := by 
  by_contra h1
  push_neg at h1
  have h4 : n < 35 := by
    omega
  have h5 : n = 1 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 ∨ n = 17 ∨ n = 19 ∨ n = 23 ∨ n = 25 ∨ n = 29 ∨ n = 31 := by
    interval_cases n <;> omega
  rcases h5 with (r | r | r | r | r | r | r | r | r | r | r)
  · -- n = 1
    rw [show n = 1 by omega] at h2 h3 h
    have h11 := h 1 0
    norm_num at h11
  · -- n = 5
    rw [show n = 5 by omega] at h2 h3 h
    have h11 := h 3 1
    norm_num at h11
  · -- n = 7
    rw [show n = 7 by omega] at h2 h3 h
    have h11 := h 1 2
    norm_num at h11
  · -- n = 11
    rw [show n = 11 by omega] at h2 h3 h
    have h11 := h 4 3
    norm_num at h11
  · -- n = 13
    rw [show n = 13 by omega] at h2 h3 h
    have h11 := h 4 1
    norm_num at h11
  · -- n = 17
    rw [show n = 17 by omega] at h2 h3 h
    have h11 := h 6 4
    norm_num at h11
  · -- n = 19
    rw [show n = 19 by omega] at h2 h3 h
    have h11 := h 3 3
    norm_num at h11
  · -- n = 23
    rw [show n = 23 by omega] at h2 h3 h
    have h11 := h 2 3
    norm_num at h11
  · -- n = 25
    rw [show n = 25 by omega] at h2 h3 h
    have h11 := h 1 3
    norm_num at h11
  · -- n = 29
    rw [show n = 29 by omega] at h2 h3 h
    have h11 := h 5 1
    norm_num at h11
  · -- n = 31
    rw [show n = 31 by omega] at h2 h3 h
    have h11 := h 5 0
    norm_num at h11