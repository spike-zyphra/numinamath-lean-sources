import Mathlib

theorem number_theory_14204 (a : ℕ → ℕ) (ha10 : a 10 = 10)
    (han : ∀ n, 10 < n → a n = 100 * a (n - 1) + n) :
    IsLeast {n : ℕ | 10 < n ∧ 99 ∣ a n} 45 := by
  constructor
  · -- Show that 45 belongs to the set, i.e., 10 < 45 and 99 divides a 45
    constructor
    · norm_num
    · -- Prove that 99 divides a 45
      norm_num [ha10, han]
      <;> omega
  · -- Show that 45 is the smallest element, i.e., if n < 45 and n > 10, then 99 does not divide a n
    intro n hn
    rcases hn with ⟨hn1, hdiv⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [ha10, han] at hdiv <;> omega