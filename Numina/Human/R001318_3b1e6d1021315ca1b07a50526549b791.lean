import Mathlib

/-Suppose $(b_a)^2=71_a$, where $a$ and $b$ represent two distinct digits. If $b=a-1$, find $a$.-/
theorem number_theory_23437 {a b : ℕ} (hb : b = (a : ℤ) - 1) (h : (Nat.ofDigits a [b]) ^ 2 = Nat.ofDigits a [1, 7]) : a = 9 := by
  -- expand the expressions at h
  repeat rw [Nat.ofDigits] at h
  zify at h
  rw [hb] at h
  ring_nf at h
  -- show that a(a - 9) = 0
  replace h : a * ((a : ℤ) - 9) = 0 := by
    ring_nf at h ⊢
    linarith only [h]
  -- show that a = 0 or a - 9 = 0
  apply Int.eq_zero_or_eq_zero_of_mul_eq_zero at h
  cases h with
  | inr h => -- when a - 9 = 0
    linarith only [h]
  | inl h => -- when a = 0
    rw [h] at hb
    norm_num at hb
    aesop
