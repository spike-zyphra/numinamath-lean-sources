import Mathlib

theorem number_theory_277424 (n : ℕ) (h : n > 0) :
    IsLeast {k | ∃ x y z, k = x * y * z ∧ x > 0 ∧ y > 0 ∧ z > 0 ∧ x * 3 = y * 4 ∧ y * 4 = z * 5} 3600 := by
  constructor
  · -- Show that 3600 is in the set
    use 20, 15, 12
    all_goals norm_num
  · -- Show that 3600 is minimal
    intro k hk
    rcases hk with ⟨x, y, z, h_eq, hx, hy, hz, heq1, heq2⟩
    have h1 : x * 3 = y * 4 := by linarith
    have h2 : y * 4 = z * 5 := by linarith
    -- deduce that y must be a multiple of 15
    have h5 : y % 15 = 0 := by
      have h_y1 : 3 ∣ y := by
        omega
      have h_y2 : 5 ∣ y := by
        omega
      have h_y3 : (3).Coprime (5) := by
        norm_num
      have h6 : 3 * 5 ∣ y := by
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h_y3 h_y1 h_y2
      have h7 : 15 ∣ y := by 
        norm_num at h6 ⊢
        exact h6
      have h8 : y % 15 = 0 := by
        omega
      exact h8
    -- So y is a multiple of 15, i.e., y = 15 * m for some m > 0
    have h8 : ∃ m, y = 15 * m := by
      refine' ⟨y / 15, by 
        omega
      ⟩
    rcases h8 with ⟨m, hm⟩
    -- Substitute y = 15 * m into the equations
    -- From x * 3 = y * 4 = (15 * m) * 4 = 60 * m, we get x = 20 * m
    have h9 : 3 * x = 4 * (15 * m) := by
      rw [hm] at h1
      linarith
    have h10 : x = 20 * m := by
      omega
    -- From y * 4 = z * 5 = (15 * m) * 4 = 60 * m, we get z = 12 * m
    have h11 : 4 * (15 * m) = 5 * z := by
      rw [hm] at h2
      linarith
    have h12 : z = 12 * m := by
      omega
    -- Substitute x, y, z back into k = x * y * z
    -- k = (20 * m) * (15 * m) * (12 * m) = 20 * 15 * 12 * m^3 = 3600 * m^3
    have h13 : k = 3600 * (m ^ 3) := by
      rw [show k = x * y * z by linarith [h_eq]]
      rw [h10, hm, h12]
      ring_nf
    -- Since k > 0, m must be positive
    have h14 : m > 0 := by
      by_contra h15
      push_neg at h15
      have hm' : m = 0 := by
        omega
      rw [hm'] at hm
      nlinarith
    -- Since m > 0, m^3 >= 1, so k >= 3600
    have h18 : k ≥ 3600 := by
      nlinarith [h13, sq_nonneg (m : ℕ), sq_nonneg ((m : ℕ) ^ 2), h14]
    linarith [h18]