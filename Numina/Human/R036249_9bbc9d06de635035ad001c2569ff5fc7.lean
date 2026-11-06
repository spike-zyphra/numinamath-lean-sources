import Mathlib

open Polynomial

/- $1 \cdot 47$ Let $x^{2}-x+a$ divide $x^{13}+x+90$, determine the positive integer value of $a$.
(24th Putnam Mathematical Competition, 1963) -/
theorem algebra_125275 {a : ℕ} (ha : a > 0) (h : (X^2 - X + C (a : ℤ) : Polynomial ℤ) ∣ (X^13 + X + 90 : Polynomial ℤ)) : a = 2 := by
  -- extract divisor polynomial q
  obtain ⟨q, h⟩ := h
  -- evaluate the expression at -1, 0, 1
  replace h (x : ℤ) : (X ^ 13 + X + 90).eval x = (X ^ 2 - X + C (a : ℤ)).eval x * q.eval x := by
    rw [h]
    exact Polynomial.eval_mul
  have h₁ := h (-1)
  simp at h₁
  have h₂ := h 0
  simp at h₂
  have h₃ := h 1
  simp at h₃
  -- from evaluation at 0, 1 we get a ∣ 2
  have ha : a ∣ 2 := by
    zify
    use q.eval 1 - q.eval 0
    linarith
  -- so a = 1 or 2, we'll prove a ≠ 1
  have : a = 1 ∨ a = 2 := by refine (Nat.dvd_prime (by norm_num)).mp ha
  apply Or.resolve_left this
  -- if a = 1 thne 3 ∣ 88 from evaluation at -1, impossible.
  rintro ha
  rw [ha] at h₁
  push_cast at h₁
  omega