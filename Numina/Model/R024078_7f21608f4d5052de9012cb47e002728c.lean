import Mathlib

theorem number_theory_116642 (p : ℕ) (hp : p ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ p^n + 3^n ∣ p^(n + 1) + 3^(n + 1) ↔ p = 3 ∨ p = 6 ∨ p = 15 := by
  by_cases h : p ≤ 15
  · -- If p ≤ 15, we can check all values
    have hp1 : p ≤ 15 := h
    have : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 := by
      omega
    rcases this with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- p = 1
      use 0
      simp
    · -- p = 2
      use 0
      simp
    · -- p = 3
      use 1
      simp
      <;> omega
    · -- p = 4
      use 0
      simp
    · -- p = 5
      use 0
      simp
    · -- p = 6
      use 1
      simp
      <;> omega
    · -- p = 7
      use 0
      simp
    · -- p = 8
      use 0
      simp
    · -- p = 9
      use 0
      simp
    · -- p = 10
      use 0
      simp
    · -- p = 11
      use 0
      simp
    · -- p = 12
      use 0
      simp
    · -- p = 13
      use 0
      simp
    · -- p = 14
      use 0
      simp
    · -- p = 15
      use 1
      simp
      <;> omega
  · -- p > 15
    push_neg at h
    use 0
    simp [h]
    <;> omega