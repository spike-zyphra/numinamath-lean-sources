import Mathlib

theorem algebra_10448 (θ : ℕ) (h : 252 / θ = (3 * 10 + θ) + θ) : θ = 6 := by
  have h1 : θ ≤ 252 := by
    by_contra h2
    push_neg at h2
    have h3 : 252 / θ = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    rw [h3] at h
    omega

  interval_cases θ <;> norm_num at h
    <;> omega