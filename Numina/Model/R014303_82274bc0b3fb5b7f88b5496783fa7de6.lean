import Mathlib

theorem algebra_228229 {x y z : ℕ} (h₀ : x = 2 * y) (h₁ : z % y = 0)
    (h₂ : 3 * z = x + 25) (h₃ : x + y + z ≥ 70) :
    x + y + z = 100 := by
  subst x
  have h4 : y > 0 := by
    by_contra h
    have h5 : y = 0 := by
      omega
    subst y
    omega
  have h5 : y ∣ z := by 
    have h6 : z % y = 0 := h₁
    exact Nat.dvd_of_mod_eq_zero h6
  rcases h5 with ⟨k, hk⟩
  rw [hk] at h₂
  have h8 : 3 * k * y = 2 * y + 25 := by 
    ring_nf at h₂ ⊢
    linarith
  have h9 : k > 0 := by
    by_contra h
    have h10 : k = 0 := by
      omega
    rw [h10] at h8
    nlinarith
  have h10 : k = 1 ∨ k = 9 := by
    have h11 : k ≤ 9 := by
      nlinarith [h8, h4]
    interval_cases k <;> omega
  rcases h10 with hk1 | hk9
  · -- if k = 1, then y = 25, total = 100
    have hy1 : y = 25 := by
      rw [show k = 1 by omega] at h8
      omega
    have hz1 : z = 25 := by
      rw [show k = 1 by omega] at hk
      nlinarith [hy1]
    omega
  · -- if k = 9, then y = 1, total = 4 (contradicts to ≥ 70)
    have hy1 : y = 1 := by
      rw [show k = 9 by omega] at h8
      omega
    have hz1 : z = 9 := by
      rw [show k = 9 by omega] at hk
      nlinarith [hy1]
    omega