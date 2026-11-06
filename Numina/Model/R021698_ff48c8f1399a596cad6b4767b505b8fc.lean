import Mathlib

theorem algebra_246923 (m n : ℝ × ℝ) (hm : m ≠ 0) (hn : n ≠ 0)
    (u v w z : ℝ × ℝ)
    (hu : u = m + 3 * n)
    (hv : v = 7 * m - 5 * n)
    (hw : w = m - 4 * n)
    (hz : z = 7 * m - 2 * n)
    (hperp : u.1 * v.1 + u.2 * v.2 = 0 ∧ w.1 * z.1 + w.2 * z.2 = 0) :
    Real.arccos ((m.1 * n.1 + m.2 * n.2) / (Real.sqrt (m.1 ^ 2 + m.2 ^ 2) * Real.sqrt (n.1 ^ 2 + n.2 ^ 2))) = 60 * Real.pi / 180 := by
  rcases hperp with ⟨huv, hwz⟩
  simp [hu, hv] at huv
  simp [hw, hz] at hwz
  have eq1 : 7 * (m.1 ^ 2 + m.2 ^ 2) + 16 * (m.1 * n.1 + m.2 * n.2) - 15 * (n.1 ^ 2 + n.2 ^ 2) = 0 := by
    ring_nf at huv ⊢
    linarith
  have eq2 : 7 * (m.1 ^ 2 + m.2 ^ 2) - 30 * (m.1 * n.1 + m.2 * n.2) + 8 * (n.1 ^ 2 + n.2 ^ 2) = 0 := by
    ring_nf at hwz ⊢
    linarith
  have eq3 : 46 * (m.1 * n.1 + m.2 * n.2) - 23 * (n.1 ^ 2 + n.2 ^ 2) = 0 := by
    nlinarith
  have eq4 : m.1 * n.1 + m.2 * n.2 = (1 / 2) * (n.1 ^ 2 + n.2 ^ 2) := by
    nlinarith
  have eq5 : m.1 ^ 2 + m.2 ^ 2 = n.1 ^ 2 + n.2 ^ 2 := by
    nlinarith [eq1, eq4]
  have h1 : (m.1 * n.1 + m.2 * n.2) / (Real.sqrt (m.1 ^ 2 + m.2 ^ 2) * Real.sqrt (n.1 ^ 2 + n.2 ^ 2)) = 1 / 2 := by
    have h2 : m.1 ^ 2 + m.2 ^ 2 = n.1 ^ 2 + n.2 ^ 2 := eq5
    have h3 : Real.sqrt (m.1 ^ 2 + m.2 ^ 2) * Real.sqrt (n.1 ^ 2 + n.2 ^ 2) = (Real.sqrt (n.1 ^ 2 + n.2 ^ 2)) ^ 2 := by
      have h5 : Real.sqrt (m.1 ^ 2 + m.2 ^ 2) = Real.sqrt (n.1 ^ 2 + n.2 ^ 2) := by
        rw [show m.1 ^ 2 + m.2 ^ 2 = n.1 ^ 2 + n.2 ^ 2 by linarith [h2]]
      rw [h5]
      all_goals ring
    have h7 : (m.1 * n.1 + m.2 * n.2) = (1 / 2) * (n.1 ^ 2 + n.2 ^ 2) := eq4
    have h9 : (n.1 ^ 2 + n.2 ^ 2) ≠ 0 := by
      by_contra h
      have h0 : n.1 ^ 2 + n.2 ^ 2 = 0 := by linarith
      have h11 : n.1 = 0 := by nlinarith [h0, sq_nonneg (n.1), sq_nonneg (n.2)]
      have h12 : n.2 = 0 := by nlinarith [h0, sq_nonneg (n.1), sq_nonneg (n.2)]
      have h13 : n = (0, 0) := by
        simp [Prod.ext_iff, h11, h12]
      rw [h13] at hn
      simp at hn
      all_goals linarith
    have h8 : (Real.sqrt (n.1 ^ 2 + n.2 ^ 2)) ^ 2 = (n.1 ^ 2 + n.2 ^ 2) := by 
      rw [Real.sq_sqrt]
      positivity
    rw [h3]
    rw [h8]
    have h10 : (n.1 ^ 2 + n.2 ^ 2) ≠ 0 := h9
    field_simp [h10]
    <;> nlinarith [h7]
  rw [h1]
  have h8 : Real.arccos (1 / 2) = 60 * Real.pi / 180 := by
    have h9 : Real.arccos (1 / 2) = Real.pi / 3 := by
      have h : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
      rw [← h]
      have h10 : 0 ≤ Real.pi / 3 := by linarith [Real.pi_pos]
      have h11 : Real.pi / 3 ≤ Real.pi := by linarith [Real.pi_pos]
      rw [Real.arccos_cos h10 h11]
    have h10 : Real.pi / 3 = 60 * Real.pi / 180 := by 
      ring_nf
    rw [h10] at h9
    exact h9
  exact h8