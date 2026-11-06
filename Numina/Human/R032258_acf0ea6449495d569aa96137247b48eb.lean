import Mathlib

/- 477*. What is the greatest common divisor of all numbers $7^{n+2}+8^{2 n+1}(n \in N)$? -/
theorem number_theory_113479 : IsGreatest {x | ∀ n, x ∣ 7^(n + 2) + 8^(2 * n + 1)} 57 := by
  constructor
  -- We prove that 57 divides all the numbers by induction on n
  · rw [Set.mem_setOf_eq]
    intro n
    induction' n with n hn
    · norm_num
    · -- Collecting terms appropriately, we can write the value for n+1 as 7 times the value for n plus a multiple of 57
      have : 7 ^ (n + 1 + 2) + 8 ^ (2 * (n + 1) + 1)
          = 7 * (7 ^ (n + 2) + 8 ^ (2 * n + 1)) + 57 * 8 ^ (2 * n + 1) := by ring
      rw [this]
      apply Nat.dvd_add
      · exact (Nat.Coprime.dvd_mul_left rfl).mpr hn
      · exact Nat.dvd_mul_right _ _
  · -- We prove that 57 is the greatest common divisor
    rw [upperBounds, Set.mem_setOf_eq]
    intro n hn
    rw [Set.mem_setOf_eq] at hn
    -- For n = 0, the value is exactly 57, so it can't be greater than 57
    have := hn 0
    norm_num at this
    exact Nat.le_of_dvd (by norm_num) this