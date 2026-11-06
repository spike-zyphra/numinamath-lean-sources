import Mathlib
namespace Algebra_611064

theorem Algebra_611064 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y ^ 2 = x * y) :
  (x ≥ 4) ∧ (y = 2 → x = 4) := by 
  by_cases hyone : y = 1
  · rw [hyone] at hxy
    simp at hxy
  have eq_aux : x = y ^ 2 /(y - 1) := by 
    have yneqone : y - 1 ≠ 0 := by 
      by_contra h
      have heqone : y = 1 :=sub_eq_zero.mp h
      exact hyone heqone
    field_simp
    ring_nf
    rw [← hxy]
    ring
  have ygtone : 1 < y := by 
    by_contra hnotgt
    have xge : x + y ^ 2 > x := by 
      have ypos : y ^ 2 > 0 := by positivity
      linarith
    rw [hxy] at xge
    have yleone : y ≤ 1 :=not_lt.mp hnotgt
    have hcontra : x * y ≤ x := by 
      nth_rw 2 [←mul_one x]
      exact (mul_le_mul_iff_of_pos_left hx).mpr yleone
    obtain h := not_lt.mpr hcontra
    exact h xge
  have ysubone : 0 < y - 1 := by
    linarith
  constructor
  · rw [eq_aux]
    calc
      _ = 2 + (y - 1) + 1 / (y - 1) := by 
        field_simp
        ring
      _ ≥ 2 + 2 := by
        have ineq_aux : (y - 1) + 1 / (y - 1) ≥ 2 := by 
          field_simp
          apply (le_div_iff₀ ysubone).mpr
          have ineq_aux₁ : (y - 1) * (y - 1)  + 1 - 2 * (y - 1)≥ 0 := by 
            have eq_aux : ((y - 1) - 1) ^ 2 ≥ 0 := by positivity
            have eq_aux₁ :((y - 1) - 1) ^ 2 = (y - 1) * (y - 1)  + 1 - 2 * (y - 1):= by ring
            rw [eq_aux₁] at eq_aux
            exact eq_aux
          exact sub_nonneg.mp ineq_aux₁
        linarith
      _ = 4 := by norm_num
  intro hy'
  rw [hy'] at hxy
  norm_num at hxy
  have eq1 : 4 = x * 2 - x := by 
    rw [←hxy]
    simp
  nth_rw 2 [←mul_one x] at eq1
  rw [←mul_sub x 2 1] at eq1
  norm_num at eq1
  exact Eq.symm eq1