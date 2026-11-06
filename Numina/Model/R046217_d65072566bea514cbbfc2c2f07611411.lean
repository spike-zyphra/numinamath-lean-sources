import Mathlib

theorem algebra_206287 :
  {x : ℝ | ∃ (d v₁ v₂ y : ℝ), d > 0 ∧ v₁ = 9 ∧ v₂ = 12 ∧ 
                             0 < y ∧ y < d ∧
                             y / v₁ = (2 * d - y) / v₂ ∧
                             (2 * d - y) / (v₁ + x) = y / v₂ ∧
                             x > 0} =
  {7} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the left side, so exist d, v1, v2, y satisfying the conditions. Prove x=7.
    rintro ⟨d, v₁, v₂, y, hd, hv₁, hv₂, hy1, hy2, h1, h2, hx⟩
    have eq1 : y * v₂ = v₁ * (2 * d - y) := by
      have h11 : v₁ ≠ 0 := by
        rw [hv₁]
        norm_num
      have h12 : v₂ ≠ 0 := by
        rw [hv₂]
        norm_num
      field_simp [h11, h12] at h1
      linarith
    have eq2 : (2 * d - y) * v₂ = y * (v₁ + x) := by
      have h31 : v₁ + x ≠ 0 := by
        nlinarith [show v₁ > 0 by linarith [hv₁], hx]
      have h32 : v₂ ≠ 0 := by
        rw [hv₂]
        norm_num
      field_simp [h31, h32] at h2
      linarith
    rw [hv₁] at eq1 eq2
    rw [hv₂] at eq1 eq2
    have eq3 : y = (6 / 7) * d := by
      nlinarith
    have eq4 : (2 * d - y) * (12 : ℝ) = y * (9 + x) := by
      nlinarith
    rw [eq3] at eq4
    -- Simplify the equation to solve for x
    nlinarith
  · -- Assume x=7, prove it's in the set
    intro h
    rw [h]
    use 7, 9, 12, 6
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num