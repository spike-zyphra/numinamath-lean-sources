import Mathlib

open Real Set
open scoped Real

theorem inequalities_69574 (x y z : ℝ) (hx : x ∈ Ioo 0 (π/2)) (hy : y ∈ Ioo 0 (π/2)) (hz : z ∈ Ioo 0 (π/2)) :
    (x * cos x + y * cos y + z * cos z) / (x + y + z) ≤ (cos x + cos y + cos z) / 3 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with  ⟨hy1, hy2⟩
  rcases hz with  ⟨hz1, hz2⟩
  have h1 : 0 < x + y + z := by linarith
  have h2 : 3 * (x * cos x + y * cos y + z * cos z) ≤ (x + y + z) * (cos x + cos y + cos z) := by
    have h3 : cos x > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [hx1, hx2, Real.pi_pos]
      · linarith [hx1, hx2, Real.pi_pos]
    have h4 : cos y > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [hy1, hy2, Real.pi_pos]
      · linarith [hy1, hy2, Real.pi_pos]
    have h5 : cos z > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [hz1, hz2, Real.pi_pos]
      · linarith [hz1, hz2, Real.pi_pos]
    have h6 : (x - y) * (cos x - cos y) ≤ 0 := by
      by_cases h : x ≥ y
      · -- x >= y
        have h7 : cos x ≤ cos y := by
          apply Real.cos_le_cos_of_nonneg_of_le_pi
          all_goals linarith [h, hx1, hy1, Real.pi_pos]
        nlinarith
      · -- x < y
        have h7 : cos x > cos y := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [show y ≥ x by linarith, hx1, hy1, Real.pi_pos]
        nlinarith
    have h7 : (x - z) * (cos x - cos z) ≤ 0 := by
      by_cases h : x ≥ z
      · -- x >= z
        have h8 : cos x ≤ cos z := by
          apply Real.cos_le_cos_of_nonneg_of_le_pi
          all_goals linarith [h, hx1, hz1, Real.pi_pos]
        nlinarith
      · -- x < z
        have h8 : cos x > cos z := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [show z ≥ x by linarith, hx1, hz1, Real.pi_pos]
        nlinarith
    have h8 : (y - z) * (cos y - cos z) ≤ 0 := by
      by_cases h : y ≥ z
      · -- y >= z
        have h9 : cos y ≤ cos z := by
          apply Real.cos_le_cos_of_nonneg_of_le_pi
          all_goals linarith [h, hy1, hz1, Real.pi_pos]
        nlinarith
      · -- y < z
        have h9 : cos y > cos z := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [show z ≥ y by linarith, hy1, hz1, Real.pi_pos]
        nlinarith
    have h32 : (x - y) * (cos x - cos y) + (x - z) * (cos x - cos z) + (y - z) * (cos y - cos z) ≤ 0 := by
      linarith [h6, h7, h8]
    have h22 : (x - y) * (cos x - cos y) + (x - z) * (cos x - cos z) + (y - z) * (cos y - cos z) =
        3 * (x * cos x + y * cos y + z * cos z) - (x + y + z) * (cos x + cos y + cos z) := by
      ring_nf
    linarith [h32, h22]
  have h3 : (x * cos x + y * cos y + z * cos z) / (x + y + z) ≤ (cos x + cos y + cos z) / 3 := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    linarith [h2]
  exact h3