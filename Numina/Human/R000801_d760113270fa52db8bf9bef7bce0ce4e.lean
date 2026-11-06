import Mathlib

def a : ℕ → ℚ
| 0 => default
| 1 => 2
| 2 => 3
| n + 3 => a (n + 2) / a (n + 1)

-- we first show that the denominator is non-zero
lemma lemma_1: ∀ n, 0 < n → a n ≠ 0 := by
  intro n hn
  induction' n using Nat.strongRecOn with n ih
  .
    by_cases l1: n = 0
    .
      simp [l1] at hn
    .
      by_cases l2: n = 1
      .
        simp [l2, a]
      .
        by_cases l3: n = 2
        .
          simp [l3, a]
        .
          have o: 3 ≤ n := by omega
          clear l1 l2 l3
          rw [show n = n - 3 + 3 by omega]
          simp [a]
          constructor
          .
            rw [show n - 3 + 2 = n - 1 by omega]
            have l4:= ih (n - 1)
            have o: n - 1 < n := by omega
            simp [o] at l4
            have o1: 1 < n := by omega
            simp [o1] at l4
            exact l4
          .
            rw [show n - 3 + 1 = n - 2 by omega]
            have l4:= ih (n - 2)
            have o: n - 2 < n := by omega
            simp [o] at l4
            have o1: 2 < n := by omega
            simp [o1] at l4
            exact l4


/-Let a1, a2, ... be a sequence for which
a1 = 2, a2 = 3, and an = a(n-1) / a(n-2)
for each positive integer n≥3. What is a 2006 ?-/

theorem algebra_15800: a 2006 = 3 := by

-- we show that a is 6-period

have h_period: ∀ n, 0 < n → a (n + 6) = a n := by
  intro n hn
  induction' n using Nat.strongRecOn with n ih
  .
    by_cases l1: n = 0
    .
      simp [l1] at hn
    .
      by_cases l2: n = 1
      .
        simp [l2, a]
        norm_num
      .
        by_cases l3: n = 2
        .
          simp [l3, a]
          norm_num
        .
          have o: 3 ≤ n := by omega
          clear l1 l2 l3
          rw [show n + 6 = n + 3 + 3 by omega]
          rw [a]
          rw [show n + 3 + 2 = n - 1 + 6 by omega]
          rw [show n + 3 + 1 = n - 2 + 6 by omega]
          have s:= ih (n - 1)
          have o1: n - 1 < n := by omega
          simp [o1] at s
          have o2: 1 < n := by omega
          simp [o2] at s
          have s1:= ih (n - 2)
          have o3: n - 2 < n := by omega
          simp [o3] at s1
          have o4: 2 < n := by omega
          simp [o4] at s1
          clear o1 o2 o3 o4
          rw [s, s1]
          clear s s1
          rw [show n = n - 3 + 3 by omega]
          rw [a]
          rw [show n - 3 + 3 - 1 = n - 1 by omega]
          rw [show n - 3 + 2 = n - 1 by omega]
          rw [show n - 3 + 3 - 2 = n - 2 by omega]
          rw [show n - 3 + 1 = n - 2 by omega]

-- then we can derive the value of 6k + 2
have h_eq: ∀ k, a (6 * k + 2) = 3 := by
  intro k
  induction' k with k ih
  .
    norm_num
    rw [a]
  .
    rw [show 6 * (k + 1) + 2 = 6 * k + 2 + 6 by omega]
    specialize h_period (6 * k + 2) (by omega)
    rw [h_period]
    rw [ih]

-- then we can derive the value of 2006
specialize h_eq 334
norm_num at h_eq
exact h_eq
