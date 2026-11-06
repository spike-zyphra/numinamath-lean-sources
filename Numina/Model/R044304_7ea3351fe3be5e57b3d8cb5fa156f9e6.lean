import Mathlib

theorem algebra_233102 :
    {v : ℝ | ∃ d : ℝ, v > 0 ∧ d > 0 ∧ d / (v + 5) = d / v - 20/60 ∧ d / (v - 5) = d / v + 25/60} = {45} := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume ∃ d > 0 such that the two equations hold, prove v = 45
    rintro ⟨d, hv_pos, hd_pos, h1, h2⟩
    have eq1 : d / (v + 5) = d / v - 20 / 60 := h1
    have eq2 : d / (v - 5) = d / v + 25 / 60 := h2
    have h3 : 3 * v * d = 3 * d * (v + 5) - v * (v + 5) := by
      have h11 : v + 5 ≠ 0 := by
        by_contra h
        have : v = -5 := by linarith
        linarith [hv_pos]
      have h12 : v ≠ 0 := by linarith
      field_simp [h11, h12] at eq1
      ring_nf at eq1 ⊢
      linarith
    have h4 : 12 * v * d = 12 * d * (v - 5) + 5 * v * (v - 5) := by
      have h21 : v - 5 ≠ 0 := by
        by_contra h
        have : v = 5 := by linarith
        rw [this] at h2
        field_simp at h2
        all_goals nlinarith [hd_pos]
      have h22 : v ≠ 0 := by linarith
      field_simp [h21, h22] at h2
      ring_nf at h2 ⊢
      linarith
    have eq3 : v ^ 2 + 5 * v = 15 * d := by
      nlinarith
    have eq4 : 12 * d = v ^ 2 - 5 * v := by
      nlinarith [eq3]
    have eq5 : d = 10 / 3 * v := by
      nlinarith [eq3, eq4]
    rw [eq5] at eq4
    have h5 : v * (v - 45) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- If v = 0, but we assumed v > 0
      linarith
    · -- If v - 45 = 0, so v = 45
      linarith
  · -- Assume v = 45, prove ∃d > 0 with the two equations
    intro hv
    rw [hv]
    use 150
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show the first equation holds
      norm_num
    · -- Show the second equation holds
      norm_num