import Mathlib

theorem algebra_319284 (a : ℤ) :
    (∃ x y : ℤ, (a + 1) * x ^ 2 - (a ^ 2 + 1) * x + 2 * a ^ 3 - 6 = 0 ∧
      (a + 1) * y ^ 2 - (a ^ 2 + 1) * y + 2 * a ^ 3 - 6 = 0) ↔
    a = -1 ∨ a = 0 ∨ a = 1 := by
  constructor
  · -- Assume the existence of integer roots, prove $a \in \{-1,0,1\}$
    rintro ⟨x, y, hx, hy⟩
    have eq3 : (x - y) * ((a + 1) * (x + y) - (a ^ 2 + 1)) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp eq3) with
    | inl h4 =>
      have h_eq : x = y := by linarith
      rw [show y = x by linarith [h_eq]] at hy
      have h2 : a ≤ 1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (x * (a - 1)), sq_nonneg ((a - 1) * (x + 1)), sq_nonneg (x * (x - a)), sq_nonneg ((a - 1) * (x - a)), sq_nonneg (x - a), sq_nonneg (x - (a ^ 2 + 1) / (a + 1))]
      have h3 : a ≥ -1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (x * (a - 1)), sq_nonneg ((a - 1) * (x + 1)), sq_nonneg (x * (x - a)), sq_nonneg ((a - 1) * (x - a)), sq_nonneg (x - a), sq_nonneg (x - (a ^ 2 + 1) / (a + 1))]
      interval_cases a <;> try { 
        omega
      }
    | inr h5 =>
      have h2 : a ≤ 1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (x * (a - 1)), sq_nonneg ((a - 1) * (x + 1)), sq_nonneg (x * (x - a)), sq_nonneg ((a - 1) * (x - a)), sq_nonneg (x - a), sq_nonneg (x - (a ^ 2 + 1) / (a + 1))]
      have h3 : a ≥ -1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (x * (a - 1)), sq_nonneg ((a - 1) * (x + 1)), sq_nonneg (x * (x - a)), sq_nonneg ((a - 1) * (x - a)), sq_nonneg (x - a), sq_nonneg (x - (a ^ 2 + 1) / (a + 1))]
      interval_cases a <;> try { 
        omega
      }
  · -- Assume $a \in \{-1,0,1\}$, prove there are integer solutions
    rintro (h | h | h)
    · -- a = -1
      rw [show a = -1 by linarith]
      use -4, -4
      constructor <;> norm_num
    · -- a = 0
      rw [show a = 0 by linarith]
      use 3, -2
      constructor <;> norm_num
    · -- a = 1
      rw [show a = 1 by linarith]
      use 2, -1
      constructor <;> norm_num