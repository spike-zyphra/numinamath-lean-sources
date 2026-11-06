import Mathlib

theorem number_theory_106705 (n : ℕ) : n ∣ (n^2 + 2 * n + 27) ↔ n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 27 := by
  constructor
  · -- Assume n ∣ (n^2 + 2n + 27)
    intro h
    have h1 : n ∣ (n ^ 2 + 2 * n + 27) := h
    -- We can show that $n$ divides 27
    have h2 : n ∣ 27 := by
      have h3 : n ∣ (n ^ 2 + 2 * n + 27) := h1
      -- n divides n^2 + 2n
      have h4 : n ∣ (n ^ 2 + 2 * n) := by
        use (n + 2)
        ring
      -- Then n divides 27 by subtraction
      have h5 : n ∣ ((n ^ 2 + 2 * n + 27) - (n ^ 2 + 2 * n)) := by
        apply Nat.dvd_sub'
        . exact h3
        . exact h4
      -- Simplify the expression
      have h6 : (n ^ 2 + 2 * n + 27) - (n ^ 2 + 2 * n) = 27 := by
        omega
      rw [h6] at h5
      exact h5
    have h3 : n ≤ 27 := by
      exact Nat.le_of_dvd (by norm_num) h2
    interval_cases n <;> norm_num at h1 h2 ⊢ <;> tauto
  · -- Show that if n is in the set {1,3,9,27}, then n divides n^2 + 2n + 27.
    rintro (rfl | rfl | rfl | rfl)
    · -- Check n = 1
      norm_num
    · -- Check n = 3
      norm_num
    · -- Check n = 9
      norm_num
    · -- Check n = 27
      norm_num