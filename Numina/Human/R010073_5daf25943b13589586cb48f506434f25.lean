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
  unfold dis_tr at h
  unfold dis_car at h
  unfold rel_sped at h
  unfold time_pass at h
  norm_num at h
  simp at h
  field_simp at h
  ring_nf at h
  have eq_aux : v * 8 = 720 := by 
    calc 
      _ = - 1200 + v * 16 - v * 8 + 1200 := by ring_nf
      _ = -480 + v * 8 - v * 8 + 1200 := by rw[h]
      _ = 720 := by ring
  have eq_aux' : v = 720 / 8 := by 
    rw [← eq_aux]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_right₀]
  norm_num at eq_aux'
  simpa