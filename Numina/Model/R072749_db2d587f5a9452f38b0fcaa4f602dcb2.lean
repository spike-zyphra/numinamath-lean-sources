import Mathlib

theorem algebra_55941 (d : ℝ) (h : d > 0) (v_p v_t v_j : ℝ)
    (h_v : v_t = v_p + 2) (h_j : v_j = v_t + 7) (h_d : d / v_p = d / v_t + 1 ∧ d / v_t = d / v_j + 1) :
    ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ Nat.Coprime m n ∧ d = m / n := by
  have ht : v_t = v_p + 2 := h_v
  have hj : v_j = v_p + 9 := by
    linarith [h_j, h_v]
  rcases h_d with ⟨h1, h2⟩
  rw [show v_t = v_p + 2 by linarith [h_v]] at h1
  rw [show v_j = v_p + 9 by linarith [h_j, h_v]] at h2
  rw [show v_t = v_p + 2 by linarith [h_v]] at h2
  have eq3 : v_p ≠ 0 := by
    by_contra h'
    rw [h'] at h1
    field_simp at h1
    all_goals linarith
  have eq4 : v_p + 2 ≠ 0 := by
    by_contra h'
    have h_vt : v_p = -2 := by linarith
    rw [show v_p = -2 by linarith [h_vt]] at h1
    norm_num at h1 <;> linarith
  have eq5 : v_p + 9 ≠ 0 := by
    by_contra h'
    have h_vj : v_p = -9 := by linarith
    rw [show v_p = -9 by linarith [h_vj]] at h2
    norm_num at h2 <;> linarith
  field_simp [eq3, eq4] at h1
  field_simp [eq4, eq5] at h2
  have h_v_p : v_p = 18 / 5 := by
    nlinarith [h1, h2]
  have h_d_val : d = 252 / 25 := by
    rw [show v_p = 18 / 5 by linarith [h_v_p]] at h1
    nlinarith
  use 252, 25
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · rw [h_d_val]
    norm_num