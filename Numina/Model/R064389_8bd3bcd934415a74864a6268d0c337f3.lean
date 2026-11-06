import Mathlib

theorem number_theory_138051 (a b : ℤ) (n : ℕ) : (a + b) ∣ (a ^ (2 * n + 1) + b ^ (2 * n + 1)) := by
  have h2 : (a - (-b)) ∣ (a ^ (2 * n + 1) - (-b) ^ (2 * n + 1)) := by
    apply sub_dvd_pow_sub_pow
  have h3 : a ^ (2 * n + 1) - (-b) ^ (2 * n + 1) = a ^ (2 * n + 1) + b ^ (2 * n + 1) := by
    have h4 : (-b) ^ (2 * n + 1) = - (b ^ (2 * n + 1)) := by
      have h5 : (-b) ^ (2 * n + 1) = - (b ^ (2 * n + 1)) := by
        ring_nf
        <;> simp [pow_succ]
        <;> ring
      linarith
    rw [h4]
    ring 
  rw [show a - (-b) = a + b by ring] at h2 
  rw [h3] at h2 
  exact h2