import Mathlib

open Real

theorem inequalities_212559 :
    IsLeast {M : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ M = max (max (x * y + 2 / z) (z + 2 / y)) (y + z + 1 / x)} 3 := by
  constructor
  · -- Show that 3 is achievable, using x = y = z = 1
    use 1, 1, 1
    norm_num
    <;> linarith
  · -- Show that no value smaller than 3 is in the set
    intro M h
    rcases h with ⟨x, y, z, hx, hy, hz, hM⟩
    by_contra h'
    push_neg at h'
    have h1 : max (max (x * y + 2 / z) (z + 2 / y)) (y + z + 1 / x) < (3 : ℝ) := by
      linarith [hM, h']
    have h2 : x * y + 2 / z < (3 : ℝ) := by
      have h3 : max (max (x * y + 2 / z) (z + 2 / y)) (y + z + 1 / x) ≥ (x * y + 2 / z : ℝ) := by
        simp [max_le_iff]
        all_goals
          linarith
      linarith [h3, h1]
    have h3 : z + 2 / y < (3 : ℝ) := by
      have h3 : max (max (x * y + 2 / z) (z + 2 / y)) (y + z + 1 / x) ≥ (z + 2 / y : ℝ) := by
        simp [max_le_iff]
        all_goals
          linarith
      linarith [h3, h1]
    have h4 : y + z + 1 / x < (3 : ℝ) := by
      have h3 : max (max (x * y + 2 / z) (z + 2 / y)) (y + z + 1 / x) ≥ (y + z + 1 / x : ℝ) := by
        simp [max_le_iff]
        all_goals
          linarith
      linarith [h3, h1]
    have h5 : x * y * z + 2 < 3 * z := by
      have h6 : x * y + 2 / z < (3 : ℝ) := h2
      have h7 : x * y + 2 / z = (x * y * z + 2) / z := by
        field_simp
        <;> ring
        <;> field_simp
      rw [h7] at h6
      have h8 : (x * y * z + 2) / z < (3 : ℝ) := h6
      have hz_pos : (0 : ℝ) < z := hz
      have h9 : x * y * z + 2 < 3 * z := by
        apply (div_lt_iff₀ (by linarith)).mp at h8
        nlinarith
      linarith
    have h6 : y * z + 2 < 3 * y := by
      have h7 : z + 2 / y < (3 : ℝ) := h3
      have h7' : z + 2 / y = (y * z + 2) / y := by
        field_simp
        <;> ring
        <;> field_simp
      rw [h7'] at h7
      have h8 : (y * z + 2) / y < (3 : ℝ) := h7
      have hy_pos : (0 : ℝ) < y := hy
      have h9 : y * z + 2 < 3 * y := by
        apply (div_lt_iff₀ (by linarith)).mp at h8
        nlinarith
      linarith
    have h7 : x * y + x * z + 1 < 3 * x := by
      have h8 : y + z + 1 / x < (3 : ℝ) := h4
      have h7 : y + z + 1 / x = (x * y + x * z + 1) / x := by
        field_simp
        <;> ring
        <;> field_simp
      rw [h7] at h8
      have h9 : (x * y + x * z + 1) / x < (3 : ℝ) := h8
      have hx_pos : (0 : ℝ) < x := hx
      have h10 : x * y + x * z + 1 < 3 * x := by
        apply (div_lt_iff₀ (by linarith)).mp at h9
        nlinarith
      linarith
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x * z - 1), sq_nonneg (y * z - 1),
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]