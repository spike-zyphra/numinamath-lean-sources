import Mathlib

theorem number_theory_311617 {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (h : a^4 + 13 * b = 107) :
    (a^2011 + b^2012) % 10 = 9 ∨ (a^2011 + b^2012) % 10 = 3 := by
  have h1 : a ≤ 3 := by
    by_contra h1
    push_neg at h1
    have h2 : a ^ 4 > 107 := by
      have h3 : a ≥ 4 := h1
      have h4 : a ^ 4 ≥ 256 := by
        have : a ≥ 4 := h3
        have h5 : a ^ 4 ≥ 4 ^ 4 := by apply Nat.pow_le_pow_of_le_left h3 4
        norm_num at h5 ⊢
        linarith
      linarith
    have h3 : a ^ 4 + 13 * b = 107 := h
    have h4 : a ^ 4 ≤ 107 := by linarith [show 13 * b ≥ 0 by positivity]
    linarith
  have h2 : a = 2 ∨ a = 3 := by
    interval_cases a <;> norm_num at ha ⊢
  rcases h2 with (ha2 | ha3)
  · -- a = 2
    have h3 : b = 7 := by
      rw [ha2] at h
      omega
    rw [h3, ha2]
    norm_num [Nat.pow_mod]
  · -- a = 3
    have h4 : b = 2 := by
      rw [ha3] at h
      omega
    rw [h4, ha3]
    norm_num [Nat.pow_mod]