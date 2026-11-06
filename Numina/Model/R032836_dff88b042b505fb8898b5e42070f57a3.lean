import Mathlib

theorem algebra_319604 (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : Odd n)
    (h : a + b = n) :
    a * b ≤ (n ^ 2 - 1) / 4 := by
  have h1 : b = n - a := by
    omega
  rw [h1]
  rcases hn with ⟨k, hk⟩
  have h5 : n = 2 * k + 1 := by
    linarith
  have h6 : a * (n - a) ≤ k * (k + 1) := by
    by_cases h7 : a ≤ k
    · 
      nlinarith [sq_nonneg (a - k : ℤ), sq_nonneg ((n - a) - (k + 1) : ℤ), 
        show (n : ℕ) = 2 * k + 1 from by linarith
      ]
    · 
      push_neg at h7
      have h8 : a ≥ k + 1 := by omega
      have h9 : n - a ≤ k := by
        omega
      nlinarith [sq_nonneg (a - (k + 1) : ℤ), sq_nonneg ((n - a) - k : ℤ), 
        show (n : ℕ) = 2 * k + 1 from by linarith
      ]
  have h7 : (n ^ 2 - 1) / 4 = k * (k + 1) := by
    rw [show n = 2 * k + 1 by linarith]
    ring_nf
    <;> omega
  linarith [h6, h7]