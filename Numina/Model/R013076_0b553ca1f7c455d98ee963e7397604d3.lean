import Mathlib

theorem number_theory_116433 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : a / b = 3 ∧ a % b = 7) (h2 : 3 * a % b = 6) :
    a = 52 ∧ b = 15 := by

  have h11 : a / b = 3 := h1.1
  have h12 : a % b = 7 := h1.2
  have h3 : a = 3 * b + 7 := by
    rw [←Nat.div_add_mod a b]
    rw [h11, h12]
    all_goals omega

  have h4 : 3 * a % b = 6 := h2
  rw [show 3 * a = 9 * b + 21 by omega] at h4
  have h5 : (9 * b + 21) % b = 6 := h4

  -- Simplify congruence to 21 mod b = 6
  have h6 : (9 * b + 21) % b = (21) % b := by
    simp [Nat.add_mod, Nat.mul_mod, show b > 0 by omega]
  rw [h6] at h5

  -- Now need to determine the value of b.
  have h9 : b ≤ 21 := by
    by_contra h8
    push_neg at h8
    have h8' : 21 % b = 21 := by
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    omega

  interval_cases b <;> norm_num at h5 <;> omega