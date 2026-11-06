import Mathlib

namespace Algebra_610951

noncomputable def dis_tr : ℝ := 1 / (4 : ℝ)

noncomputable def dis_car : ℝ := 3 / (3600 : ℝ) * 75

def rel_sped (v₁ : ℝ) (v₂ : ℝ) : ℝ := v₁ - v₂

noncomputable def time_pass (x : ℝ) (v : ℝ): ℝ := x/ v

end Algebra_610951

open Algebra_610951

theorem Algebra_610951 {v : ℝ} (h : time_pass dis_tr (rel_sped v 60) = 2 * (time_pass dis_car (rel_sped v 75))) 
  (neq₁ : (v - 60) ≠ 0) (neq₂ : (v - 75) ≠ 0)
  : v = 90 := by 
  rw [time_pass, rel_sped, dis_tr] at h
  rw [time_pass, rel_sped, dis_car] at h
  have h1 : v - 60 ≠ 0 := neq₁
  have h2 : v - 75 ≠ 0 := neq₂
  field_simp [h1, h2] at h
  linarith