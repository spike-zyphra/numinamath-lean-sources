import Mathlib

/-Determine the smallest natural number n for which there exists a natural number x such that the equation
(x+1)^3+(x+2)^3+(x+3) ^3+(x+4)^3=(x+n)^3 holds true-/

 -- we show an important factorization lemma
lemma lemma_1 (x: ℤ): (x + 1) ^ 3 + (x + 2) ^ 3 + (x + 3) ^ 3 + (x + 4) ^ 3 =
  2 * (2 * x + 5) * (x ^ 2 + 5 * x + 10) := by ring

theorem algebra_619416: IsLeast {n: ℤ | 0 ≤ n ∧ ∃ x: ℤ, 0 ≤ x ∧
(x + 1) ^ 3 + (x + 2) ^ 3 + (x + 3) ^ 3 + (x + 4) ^ 3 = (x + n) ^ 3} 10 := by

  constructor

  -- the forward direction
  .
    simp
    use 10
    norm_num

  -- the backward direction
  .
    intro n h
    simp only [Set.mem_setOf_eq] at h
    rcases h with ⟨hn, h⟩
    obtain ⟨x, hx⟩ := h
    rcases hx with ⟨hx, h⟩
    rw [lemma_1] at h
    by_contra! l
    replace l: n ≤ 9 := by omega
    have f: 2 * (2 * x + 5) * (x ^ 2 + 5 * x + 10) ≤ (2 * x + 5) * (x + 9) ^ 2 := by
      rw [h]
      rw [show (x + n) ^ 3 = (x + n) * (x + n) ^ 2 by ring]
      have o1: (x + n) ^ 2 ≤ (x + 9) ^ 2 := by
        nlinarith
      nlinarith
    replace f: 2 * (x ^ 2 + 5 * x + 10) ≤ (x + 9) ^ 2 := by
      nlinarith
    replace f: 0 ≤ (x + 9) ^ 2 - 2 * (x ^ 2 + 5 * x + 10) := by linarith
    rw [show (x + 9) ^ 2 - 2 * (x ^ 2 + 5 * x + 10) = - x ^ 2 + 8 * x + 61 by ring] at f
    have lx: x < 13 := by nlinarith
    clear f
    interval_cases x <;> interval_cases n <;> simp at h