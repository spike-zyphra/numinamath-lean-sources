import Mathlib

theorem algebra_301670 {a b : ℕ → ℤ} (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (han : ∀ n, a (n + 1) = a n + 2 * b n) (hbn : ∀ n, b (n + 1) = a n + b n) :
    a 2001 ^ 2 - 2 * b 2001 ^ 2 = 1 := by
  have h : ∀ n, a n ^ 2 - 2 * b n ^ 2 = (-1 : ℤ) ^ (n + 1) := by 
    intro n
    induction n with 
    | zero =>
      rw [ha0, hb0]
      norm_num
    | succ n ih =>
      have ha1 : a (n + 1) = a n + 2 * b n := by 
        apply han
      have hb1 : b (n + 1) = a n + b n := by 
        apply hbn
      calc
        a (n + 1) ^ 2 - 2 * b (n + 1) ^ 2 
            = (a n + 2 * b n) ^ 2 - 2 * (a n + b n) ^ 2 := by rw [ha1, hb1]
        _ = (a n ^ 2 + 4 * a n * b n + 4 * b n ^ 2) - 2 * (a n ^ 2 + 2 * a n * b n + b n ^ 2) := by
          ring
        _ = - (a n ^ 2 - 2 * b n ^ 2) := by 
          ring_nf
        _ = - ((-1 : ℤ) ^ (n + 1)) := by rw [ih]
        _ = (-1 : ℤ) ^ ((n + 1) + 1) := by 
          ring_nf
  have h2001 := h 2001
  rw [h2001]
  norm_num