import Mathlib

theorem number_theory_263465 (x : ℕ) (hx : x < 1953) (h : (1953 - x) % 9 = 0)
    (h' : (1953 - x) = (Nat.digits 10 x).sum) :
    (1953 - x) = 18 := by
  interval_cases x <;> norm_num at h h' ⊢ <;> omega