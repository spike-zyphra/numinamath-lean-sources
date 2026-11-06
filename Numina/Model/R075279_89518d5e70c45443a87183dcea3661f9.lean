import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_144226 {a α : ℝ} (ha : 0 < a) (hα : α ∈ Ioo 0 π) :
    let h_a := a * tan (α / 2) / (2 * tan (α / 2) ^ 2 + 1)
    h_a ≤ (a / 2) / tan (α / 2) := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : 0 < α / 2 := by linarith
  have h2 : α / 2 < π / 2 := by linarith [Real.pi_pos]
  have htan_pos : 0 < tan (α / 2) := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    all_goals linarith
  have h3 : 0 < tan (α / 2) := htan_pos
  have h4 : 0 < 2 * tan (α / 2)^2 + 1 := by
    nlinarith [sq_nonneg (tan (α / 2)), h3]

  have h7 : a * tan (α / 2)^2 ≤ (a / 2) * (2 * tan (α / 2)^2 + 1) := by
    nlinarith [ha, sq_nonneg (tan (α / 2)), mul_pos ha (show 0 < tan (α / 2) by linarith)]

  have h8 : a * tan (α / 2) / (2 * tan (α / 2) ^ 2 + 1) ≤ (a / 2) / tan (α / 2) := by
    have h9 : 0 < tan (α / 2) := h3
    have h10 : 0 < 2 * tan (α / 2)^2 + 1 := by
      nlinarith [sq_nonneg (tan (α / 2)), h9]
    
    have h11 : a * tan (α / 2)^2 ≤ (a / 2) * (2 * tan (α / 2)^2 + 1) := h7
    have h12 : a * tan (α / 2) / (2 * tan (α / 2)^2 + 1) - (a / 2) / tan (α / 2) ≤ 0 := by
      have h13 : tan (α / 2) * (2 * tan (α / 2)^2 + 1) > 0 := by positivity
      have h14 : a * tan (α / 2) / (2 * tan (α / 2)^2 + 1) - (a / 2) / tan (α / 2) =
          (a * tan (α / 2)^2 - (a / 2) * (2 * tan (α / 2)^2 + 1)) / (tan (α / 2) * (2 * tan (α / 2)^2 + 1)) := by
        field_simp
        <;> ring
      rw [h14]
      apply div_nonpos_of_nonpos_of_nonneg
      nlinarith
      nlinarith
    linarith

  exact h8