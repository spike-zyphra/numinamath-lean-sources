import Mathlib
open Real

theorem algebra_223455 {α : ℝ}
  (hα : α ∈ Set.Ioo 0 (π/2))
  (tan_cot : tan (α/2) + cot (α/2) = 5/2)
  : sin (α - π/3) = (4 - 3 * √3) / 10
    := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : cos (α / 2) ≠ 0 := by
    have h2 : cos (α / 2) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · -- Show -π/2 < α/2
        linarith [hα1, hα2, Real.pi_pos]
      · -- Show α/2 < π/2
        linarith [hα1, hα2, Real.pi_pos]
    nlinarith
  have h2 : sin (α / 2) ≠ 0 := by
    have h3 : sin (α / 2) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · -- Show 0 < α/2
        nlinarith [hα1, hα2, Real.pi_pos]
      · -- Show α/2 < π
        linarith [hα1, hα2, Real.pi_pos]
    nlinarith
  have eq1 : tan (α / 2) + cot (α / 2) = (sin (α / 2) / cos (α / 2)) + (cos (α / 2) / sin (α / 2)) := by
    rw [tan_eq_sin_div_cos, cot_eq_cos_div_sin]
  rw [eq1] at tan_cot
  have h3 : cos (α / 2) * sin (α / 2) ≠ 0 := by
    apply mul_ne_zero
    exact h1
    exact h2
  have eq4 : cos (α / 2) * sin (α / 2) = 2 / 5 := by
    have eq5 : (sin (α / 2) / cos (α / 2)) + (cos (α / 2) / sin (α / 2)) = 1 / (cos (α / 2) * sin (α / 2)) := by
      have eq2 : cos (α / 2) * sin (α / 2) ≠ 0 := h3
      field_simp [h1, h2, eq2]
      <;> nlinarith [Real.sin_sq_add_cos_sq (α / 2)]
    have eq6 : 1 / (cos (α / 2) * sin (α / 2)) = 5 / 2 := by
      linarith [tan_cot, eq5]
    have eq7 : cos (α / 2) * sin (α / 2) = 2 / 5 := by
      have eq8 : cos (α / 2) * sin (α / 2) ≠ 0 := h3
      field_simp [eq8] at eq6 ⊢
      <;> nlinarith
    exact_mod_cast eq7
  have h4 : sin α = 4 / 5 := by
    have h5 : sin α = 2 * sin (α / 2) * cos (α / 2) := by
      rw [←sin_two_mul]
      ring_nf
    rw [h5]
    have h6 : 2 * (sin (α / 2) * cos (α / 2)) = 4 / 5 := by
      have h8 : sin (α / 2) * cos (α / 2) = 2 / 5 := by
        linarith [eq4]
      nlinarith
    linarith
  have h5 : cos α > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · -- Show -π/2 < α
      nlinarith [hα1, hα2, Real.pi_pos]
    · -- Show α < π/2
      nlinarith [hα1, hα2, Real.pi_pos]
  have h6 : cos α = 3 / 5 := by
    have h7 : cos α ^ 2 + sin α ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq α
    rw [h4] at h7
    have h8 : cos α ^ 2 = 9 / 25 := by
      nlinarith
    have h9 : cos α = 3 / 5 := by
      nlinarith [sq_pos_of_pos h5]
    exact_mod_cast h9
  have h7 : sin (α - π / 3) = sin α * cos (π / 3) - cos α * sin (π / 3) := by
    rw [sin_sub]
  rw [h7]
  have h10 : cos (π / 3) = 1 / 2 := by
    exact cos_pi_div_three
  have h11 : sin (π / 3) = Real.sqrt 3 / 2 := by
    rw [sin_pi_div_three]
  rw [h4, h6, h10, h11]
  field_simp
  <;> ring_nf <;> field_simp
  <;> ring