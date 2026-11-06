import Mathlib

open Real

namespace algebra_616488

lemma mono : StrictMonoOn (fun x : ℝ => (5 : ℝ) ^ x - 2 ^ x) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hxy' : 0 < y - x := sub_pos.mpr hxy
  simp only
  suffices : 2 ^ x * (2 ^ (y - x) - 1)  < (5 : ℝ) ^ x * (5 ^ (y - x) - 1)
  ring_nf at this
  have eq1 : (5 : ℝ) ^ x * 5 ^ (y - x) = 5 ^ y := by
    rw [← rpow_add (by norm_num)]
    simp
  have eq2 : (2 : ℝ) ^ x * 2 ^ (y - x) = 2 ^ y := by
    rw [← rpow_add (by norm_num)]
    simp
  rw [eq1, eq2] at this
  linarith only [this]
  have lt1 : 0 < (5 : ℝ) ^ (y - x) - 1 := by
    simp
    apply one_lt_rpow (by norm_num) hxy'
  have lt2 : 0 < (2 : ℝ) ^ (y - x) - 1 := by
    simp
    apply one_lt_rpow (by norm_num) hxy'
  gcongr
  simpa using hx
  all_goals norm_num

end algebra_616488

open algebra_616488

theorem algebra_616488 {x : ℝ} : (5 : ℝ) ^ x - 2 ^ x = 3093 ↔ x = 5 := by
  constructor
  · -- Assume (5 : ℝ) ^ x - 2 ^ x = 3093, prove x = 5
    intro h_eq
    have h1 : (5 : ℝ) ^ (x : ℝ) - (2 : ℝ) ^ (x : ℝ) = (3093 : ℝ) := by linarith
    have h2 : x > (0 : ℝ) := by
      by_contra h
      push_neg at h
      have h3 : (5 : ℝ) ^ x ≤ (1 : ℝ) := by
        have h4 : (5 : ℝ) ^ (x : ℝ) ≤ (5 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals nlinarith
        have h5 : (5 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
          simp
        nlinarith
      have h4 : (2 : ℝ) ^ x ≥ (0 : ℝ) := by
        positivity
      have h3' : (5 : ℝ) ^ x - (2 : ℝ) ^ x ≤ (1 : ℝ) := by
        nlinarith
      nlinarith
    have h3 : (5 : ℝ) ^ (5 : ℝ) - (2 : ℝ) ^ (5 : ℝ) = (3093 : ℝ) := by norm_num
    have h4 : x = (5 : ℝ) := by
      have h5 : x ≤ (5 : ℝ) := by
        by_contra h
        push_neg at h
        -- Assume x > 5, show a contradiction
        have eq1 : (5 : ℝ) ^ (5 : ℝ) - (2 : ℝ) ^ (5 : ℝ) = (3093 : ℝ) := by norm_num
        have eq2 : (5 : ℝ) ^ (5 : ℝ) - (2 : ℝ) ^ (5 : ℝ) < (5 : ℝ) ^ x - (2 : ℝ) ^ x := by
          have h5 : (5 : ℝ) < x := by linarith
          have h55 : (5 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
            norm_num
          have hxx : x ∈ Set.Ioi (0 : ℝ) := by
            have : x > (0 : ℝ) := h2
            exact this
          have h555 : (5 : ℝ) < x := by linarith
          apply mono h55 hxx h555
        nlinarith
      -- Now prove x ≥ 5
      have h6 : x ≥ (5 : ℝ) := by
        by_contra h
        push_neg at h
        -- Assume x < 5, show a contradiction
        have eq1 : (5 : ℝ) ^ (5 : ℝ) - (2 : ℝ) ^ (5 : ℝ) = (3093 : ℝ) := by norm_num
        have eq2 : (5 : ℝ) ^ x - (2 : ℝ) ^ x < (5 : ℝ) ^ (5 : ℝ) - (2 : ℝ) ^ (5 : ℝ) := by
          have h5 : x < (5 : ℝ) := by linarith
          have h55 : x ∈ Set.Ioi (0 : ℝ) := by
            have : x > (0 : ℝ) := h2
            exact this
          have hxx : (5 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
            norm_num
          have h555 : x < (5 : ℝ) := by linarith
          apply mono h55 hxx h555
        nlinarith
      linarith
    tauto
  · -- Assume x = 5, prove the equation
    intro h_eq
    rw [h_eq]
    all_goals norm_num