import Mathlib

open Fin

/- The sequence $(a_n)$ is defined by $a_0 = 2,$ $a_1 = 1,$ and
\[a_n = a_{n - 1} \sqrt{3} - a_{n - 2}\]for all $n \ge 2.$  Find $a_{100}.$ -/
theorem algebra_20891 {a : ℕ → ℝ} (ha0 : a 0 = 2) (ha1 : a 1 = 1)
    (han : ∀ n, a (n + 2) = a (n + 1) * Real.sqrt 3 - a n) :
    a 100 = Real.sqrt 3 - 4 := by
  -- $a_n$ is periodic with period $12$
  have periodan (n : ℕ) : a (12 * n) = a 0 ∧ a (12 * n + 1) = a 1 := by
    induction' n with n hn
    simp only [mul_zero, zero_add, and_self]
    have h0 := hn.1
    have h1 := hn.2
    rw [ha0] at h0
    rw [ha1] at h1
    have h2 : a (12 * n + 2) = Real.sqrt 3 - 2 := by
      rw [han, h0, h1]
      ring
    have h3 : a (12 * n + 3) = 2 - 2 * Real.sqrt 3 := by
      rw [han, h1, h2]
      ring_nf
      rw [Real.sq_sqrt (by exact zero_le_three)]
      ring
    have h4 : a (12 * n + 4) = Real.sqrt 3 - 4 := by
      rw [han, h2, h3]
      ring_nf
      rw [Real.sq_sqrt (by exact zero_le_three)]
      ring
    have h5 : a (12 * n + 5) = 1 - 2 * Real.sqrt 3 := by
      rw [han, h3, h4]
      ring_nf
      rw [Real.sq_sqrt (by exact zero_le_three)]
      ring
    have h6 : a (12 * n + 6) = -2 := by
      rw [han, h4, h5]
      ring_nf
      rw [Real.sq_sqrt (by exact zero_le_three)]
      ring
    have h7 : a (12 * n + 7) = -1 := by
      rw [han, h5, h6]
      ring_nf
    have h8 : a (12 * n + 8) = 2 - Real.sqrt 3 := by
      rw [han, h6, h7]
      ring_nf
    have h9 : a (12 * n + 9) = 2 * Real.sqrt 3 - 2 := by
      rw [han, h7, h8]
      ring_nf
      rw [Real.sq_sqrt (by exact zero_le_three)]
      ring
    have h10 : a (12 * n + 10) = 4 - Real.sqrt 3 := by
      rw [han, h8, h9]
      ring_nf
      rw [Real.sq_sqrt (by exact zero_le_three)]
      ring
    have h11 : a (12 * n + 11) = 2 * Real.sqrt 3 - 1 := by
      rw [han, h9, h10]
      ring_nf
      rw [Real.sq_sqrt (by exact zero_le_three)]
      ring
    have h12 : a (12 * n + 12) = 2 := by
      rw [han, h10, h11]
      ring_nf
      rw [Real.sq_sqrt (by exact zero_le_three)]
      ring
    have h13 : a (12 * n + 13) = 1 := by
      rw [han, h11, h12]
      ring_nf
    rw [mul_add, add_assoc, h12, h13, ha0, ha1]
    simp only [and_self]
  -- So $a_96 = a_0 = 2, a_97 = a_1 = 1$
  have a96 : a 96 = 2 := by 
    rw [(periodan 8).1, ha0]
  have a97 : a 97 = 1 := by 
    rw [(periodan 8).2, ha1]
  -- So $a_100 = \sqrt{3} - 4$
  have a98 : a 98 = Real.sqrt 3 - 2 := by
    rw [han, a96, a97]
    ring
  have a99 : a 99 = 2 - 2 * Real.sqrt 3 := by
    rw [han, a97, a98]
    ring_nf
    rw [Real.sq_sqrt (by exact zero_le_three)]
    ring
  have a100 : a 100 = Real.sqrt 3 - 4 := by
    rw [han, a98, a99]
    ring_nf
    rw [Real.sq_sqrt (by exact zero_le_three)]
    ring
  exact a100