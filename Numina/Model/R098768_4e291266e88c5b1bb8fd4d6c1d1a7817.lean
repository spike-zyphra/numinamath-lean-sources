import Mathlib

theorem number_theory_231508 (x : ℝ) (hx : x = 0.123456789) (h : (Nat.floor (10^25 * x)) % 10 = 5) :
    (Nat.floor (10^5 * x)) % 10 = 9 := by
  rw [hx] at h
  norm_num at h <;> all_goals
    norm_num at h ⊢
    all_goals omega