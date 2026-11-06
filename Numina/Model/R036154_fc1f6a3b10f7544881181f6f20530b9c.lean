import Mathlib

open Nat

theorem AMC_Algebra_1158
  (x y a b m: ℤ)
  (hx : x = 10 * a + b)
  (hy : y = 10 * b + a)
  (heq : x * x - y * y = m * m)
  (ha1 : a > 0)
  (ha2 : a < 10)
  (hb1 : b > 0)
  (hb2 : b < 10)
  (hm : m > 0)
  : x + y + m = 154 := by 
  rw [hx, hy] at heq
  have h1 : m ^ 2 = 99 * (a ^ 2 - b ^ 2) := by
    nlinarith
  have h2 : a ≤ 9 := by omega
  have h3 : b ≤ 9 := by omega
  have h4 : m ^ 2 % 11 = 0 := by
    have eq1 : m ^ 2 = 99 * (a ^ 2 - b ^ 2) := h1
    rw [eq1]
    omega
  have h5 : m % 11 = 0 := by 
    have h6 : m ^ 2 % 11 = 0 := h4
    have h7 : m % 11 = 0 := by
      have h11 : m % 11 = 0 ∨ m % 11 = 1 ∨ m % 11 = 2 ∨ m % 11 = 3 ∨ m % 11 = 4 ∨ m % 11 = 5 ∨ m % 11 = 6 ∨ m % 11 = 7 ∨ m % 11 = 8 ∨ m % 11 = 9 ∨ m % 11 = 10 := by
        omega
      rcases h11 with (h | h | h | h | h | h | h | h | h | h | h) <;> 
        simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod] at h6 <;> 
          omega
    exact h7
  have h8 : ∃ k : ℤ, m = 11 * k := by 
    refine' ⟨m / 11, by omega⟩
  rcases h8 with ⟨k, hk⟩
  have h9 : m ^ 2 = 121 * (k ^ 2) := by 
    rw [hk]
    ring
  have h10 : 121 * (k ^ 2) = 99 * (a ^ 2 - b ^ 2) := by
    nlinarith [h1, h9]
  have h11 : a ≤ 9 := by omega
  have h12 : b ≤ 9 := by omega
  have h14 : k ^ 2 ≤ 99 := by
    nlinarith [sq_nonneg (k * 11 - 0), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (k), sq_nonneg (a - b), sq_nonneg (a + b),
      show a ≤ 9 by omega, show b ≤ 9 by omega, sq_pos_of_pos hm
    ]
  have hk8 : k ≤ 9 := by
    nlinarith [show k ^ 2 ≥ 0 by nlinarith]
  have hk9 : k ≥ -9 := by
    nlinarith [show k ^ 2 ≥ 0 by nlinarith]
  interval_cases k <;> try { 
    omega
  } <;> try { 
    interval_cases a <;> try { 
      omega
    } <;> try { 
      interval_cases b <;> omega
    }
  }