import Mathlib

theorem algebra_315444 {n : ℝ} (h : ∃ x1 x2, x1 ≠ x2 ∧ 4*x1^2-8*n*x1-3*n-2=0 ∧ 4*x2^2-8*n*x2-3*n-2=0 ∧
    ∃ m : ℤ, (x1-x2)^2=m ∧ m^2-(n+3)*m-2*n^2+2=0) :
    n=0 := by

  rcases h with ⟨x1, x2, hx12, h1, h2, ⟨m, hm1, hm2⟩⟩

  have h3 : (x1 - x2) ^ 2 = (4 * n ^ 2 + 3 * n + 2 : ℝ) := by
    have h6 : x1 + x2 = 2 * n := by
      have h_sub : 4 * (x1^2 - x2^2) - 8 * n * (x1 - x2) = 0 := by linarith
      have h_sub2 : (x1 - x2) * (4 * (x1 + x2) - 8 * n) = 0 := by
        ring_nf at h_sub ⊢
        linarith
      have h4 : x1 - x2 ≠ 0 := by
        intro h3
        apply hx12
        linarith
      have h5 : 4 * (x1 + x2) - 8 * n = 0 := by
        apply (mul_left_inj' h4).mp
        linarith
      linarith

    have h7 : 4 * (x1 ^ 2 + x2 ^ 2) - 8 * n * (x1 + x2) - 6 * n - 4 = 0 := by
      nlinarith

    have h8 : 4 * (x1 ^ 2 + x2^2) = 4 * (x1 + x2)^2 - 8 * (x1 * x2) := by
      nlinarith [sq_nonneg (x1 - x2)]

    rw [h8] at h7
    rw [h6] at h7

    have h9 : x1 * x2 = - (3 * n + 2) / 4 := by
      nlinarith

    have h10 : (x1 - x2) ^ 2 = 4 * n ^ 2 + 3 * n + 2 := by
      nlinarith [h6, h9]
    linarith

  have h4 : (x1 - x2) ^ 2 = (m : ℝ) := by 
    exact_mod_cast hm1

  have h5 : (m : ℝ) = 4 * n ^ 2 + 3 * n + 2 := by
    linarith [h3, h4]

  have h7 : (m : ℝ) ^ 2 - (n + 3) * (m : ℝ) - 2 * n ^ 2 + 2 = 0 := by
    exact_mod_cast hm2

  rw [show (m : ℝ) = 4 * n ^ 2 + 3 * n + 2 by linarith [h5]] at h7

  have h8 : n * (4 * n + 1) * (2 * n + 1) ^ 2 = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h8) with h9 h10
  · cases' (mul_eq_zero.mp h9) with h11 h12
    · -- h11: n = 0
      linarith
    · -- h12: 4n + 1 = 0
      have h13 : n = -1 / 4 := by linarith
      have h14 : (m : ℝ) = (3 / 2 : ℝ) := by
        rw [show (m : ℝ) = 4 * n ^ 2 + 3 * n + 2 by linarith [h5]]
        rw [h13]
        norm_num
      have h18 : (2 * m : ℝ) = (3 : ℝ) := by
        nlinarith
      have h19 : 2 * m = 3 := by
        exact_mod_cast h18
      omega
  · -- h10: (2n+1)^2 = 0
    have h13 : (2 * n + 1 : ℝ) = 0 := by
      apply pow_eq_zero 
      exact h10
    have h14 : n = -1 / 2 := by
      linarith
    have h15 : (m : ℝ) = (3 / 2 : ℝ) := by
      rw [show (m : ℝ) = 4 * n ^ 2 + 3 * n + 2 by linarith [h5]]
      rw [show n = -1/2 by linarith [h14]]
      norm_num
    have h18 : (2 * m : ℝ) = (3 : ℝ) := by
      nlinarith
    have h19 : 2 * m = 3 := by
      exact_mod_cast h18
    omega