import Mathlib

theorem algebra_179607 (x : ℝ) (hx : |x| < 0.5) :
    ∑' n : ℕ, (2 * x) ^ n = 3.4 - 1.2 * x ↔ x = 1 / 3 := by
  have eq1 : ∑' n : ℕ, (2 * x) ^ n = (1 - (2 * x))⁻¹ := by
    rw [tsum_geometric_of_norm_lt_one]
    · -- prove that |2*x| < 1
      have h : ‖2 * x‖ < 1 := by
        have h4 : ‖x‖ < (0.5 : ℝ) := by simpa using hx
        have h5 : ‖(2 * x : ℝ)‖ = 2 * ‖x‖ := by
          simp [norm_mul]
          <;> ring_nf <;> norm_num
        rw [h5]
        linarith
      simpa using h
    all_goals norm_num
    all_goals norm_num
  rw [eq1]
  constructor
  · -- Forward: if the equation holds, then x = 1/3
    intro h
    have h1 : ((1 - 2 * x) : ℝ) ≠ 0 := by
      by_contra h2
      have h3 : (1 - 2 * x) = 0 := by linarith
      rw [h3] at h
      norm_num at h
      <;> try { tauto }
      all_goals try { linarith [abs_nonneg x] }
    -- Equation is (1 - 2*x)⁻¹ = 3.4 - 1.2*x
    have h2 : (1 - 2 * x) ≠ 0 := h1
    field_simp at h
    ring_nf at h
    -- Now the equation is reduced to a quadratic equation
    have h3 : (x - 1 / 3) * (x - 3) = 0 := by
      nlinarith [sq_pos_of_pos (show 0 < (0.5 : ℝ) - x by linarith [abs_lt.mp hx]), sq_nonneg (x - 1 / 3), sq_nonneg (x - 3)]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Solving gves x = 1/3
      linarith
    · -- Solving gves x = 3 which contradicts |x| < 0.5
      have h6 : x = 3 := by linarith
      rw [h6] at hx
      norm_num [abs_lt] at hx
  · -- Backward: If x = 1/3, then the equation holds
    intro h
    rw [h]
    norm_num
    <;> try { ring_nf }
    <;> try { norm_num }
    <;> try { tauto }
    all_goals try { linarith }