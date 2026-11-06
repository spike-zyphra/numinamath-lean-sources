import Mathlib

theorem algebra_311709 (m : ℕ) (hm : m > 0) (x y : ℕ)
    (h1 : x - y = 2) (h2 : m * x + y = 6) :
    m = 1 ∧ (x, y) = (4, 2) ∨ m = 3 ∧ (x, y) = (2, 0) := by
  have h3 : x = y + 2 := by
    omega
  rw [h3] at h2
  have h4 : m ≤ 3 := by
    by_contra h
    push_neg at h
    have h5 : m * (y + 2) + y ≥ 4 * (y + 2) + y := by
      have : m ≥ 4 := by omega
      have h6 : (m : ℕ) * (y + 2) ≥ (4 : ℕ) * (y + 2) := by 
        apply Nat.mul_le_mul_right
        omega
      omega
    omega
  have h5 : m > 0 := hm
  have h6 : m = 1 ∨ m = 2 ∨ m = 3 := by 
    omega
  rcases h6 with (r | r | r)
  · -- m = 1
    have hm1 : m = 1 := r
    have h7 : y = 2 := by
      rw [hm1] at h2
      omega
    have h8 : x = 4 := by
      omega
    left
    simp [hm1, h8, h7, Prod.ext_iff]
    <;> tauto
  · -- m = 2
    -- Show contradiction
    have hm2 : m = 2 := r
    rw [hm2] at h2
    omega
  · -- m = 3
    have hm3 : m = 3 := r
    have h8 : y = 0 := by
      rw [hm3] at h2
      omega
    have h9 : x = 2 := by
      omega
    right
    simp [hm3, h9, h8, Prod.ext_iff]
    <;> tauto