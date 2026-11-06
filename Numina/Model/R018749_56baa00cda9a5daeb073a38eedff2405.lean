import Mathlib

theorem number_theory_209244 (n : ℕ) (h₀ : ¬(2 ∣ n)) (h₁ : ¬(3 ∣ n))
    (h₂ : ∀ a b : ℕ, |(2 ^ a : ℤ) - 3 ^ b| ≠ n) :
    n ≥ 35 := by
  by_contra h
  push_neg at h
  have h3 : n < 35 := by linarith
  have h4 := h₂ 1 0
  have h5 : n < 35 := h3
  have h6 : n % 2 = 1 := by 
    omega
  have h7 : n % 3 = 1 ∨ n % 3 = 2 := by 
    omega
  have h8 : n = 1 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 ∨ n = 17 ∨ n = 19 ∨ n = 23 ∨ n = 25 ∨ n = 29 ∨ n = 31 := by
    interval_cases n <;> omega
  rcases h8 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · -- n = 1, pair (1, 0)
    exfalso
    specialize h₂ 1 0
    norm_num at h₂
  · -- n = 5, pair (5, 3)
    exfalso
    specialize h₂ 5 3
    norm_num at h₂
  · -- n = 7, pair (3, 0)
    exfalso
    specialize h₂ 3 0
    norm_num at h₂
  · -- n = 11, pair (4, 3)
    exfalso
    specialize h₂ 4 3
    norm_num at h₂
  · -- n = 13, pair (4, 1)
    exfalso
    specialize h₂ 4 1
    norm_num at h₂
  · -- n = 17, pair (6, 4)
    exfalso
    specialize h₂ 6 4
    norm_num at h₂
  · -- n = 19, pair (3, 3)
    exfalso
    specialize h₂ 3 3
    norm_num at h₂
  · -- n = 23, pair (5, 2)
    exfalso
    specialize h₂ 5 2
    norm_num at h₂
  · -- n = 25, pair (1, 3)
    exfalso
    specialize h₂ 1 3
    norm_num at h₂
  · -- n = 29, pair (5, 1)
    exfalso
    specialize h₂ 5 1
    norm_num at h₂
  · -- n = 31, pair (5, 0)
    exfalso
    specialize h₂ 5 0
    norm_num at h₂