import Mathlib

theorem algebra_16528 (x : ℕ) (hx : 0 < x) (h : 3 ∣ x) :
    x^3 < 1000 → x ≤ 9 := by
  intro h1
  by_contra h2
  push_neg at h2

  have h3 : x ≥ 10 := by omega

  have h4 : x ≥ 12 := by
    by_contra h5
    push_neg at h5
    interval_cases x <;> norm_num at h h3 h5 <;> all_goals omega

  have h5 : x^3 ≥ 12^3 := by
    apply Nat.pow_le_pow_of_le_left h4 3

  norm_num at h5 h1

  all_goals linarith