import Mathlib

open BigOperators Real Set

theorem algebra_311594 : {a : ℝ | ∃ f : ℝ → ℝ, f = (fun x => a * sin (2 * x) + cos (2 * x) + sin x + cos x) ∧ ∀ x, f (-π + x) = f (-π - x)} = ∅ := by 
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  rcases h with ⟨f, hf_eq, hf⟩
  have eq1 := hf (Real.pi / 2)
  have h1 : f (-π + Real.pi / 2) = f (-π - Real.pi / 2) := by
    simpa using eq1
  have eq2 : f (-π + Real.pi / 2) = a * sin (2 * (-π + Real.pi / 2)) + cos (2 * (-π + Real.pi / 2)) + sin (-π + Real.pi / 2) + cos (-π + Real.pi / 2) := by
    rw [hf_eq]
  have eq3 : f (-π - Real.pi / 2) = a * sin (2 * (-π - Real.pi / 2)) + cos (2 * (-π - Real.pi / 2)) + sin (-π - Real.pi / 2) + cos (-π - Real.pi / 2) := by
    rw [hf_eq]
  rw [eq2, eq3] at h1
  have h2 : sin (2 * (-π + Real.pi / 2)) = 0 := by
    have eq4 : 2 * (-π + Real.pi / 2) = - (Real.pi) := by
      nlinarith [Real.pi_pos]
    rw [eq4]
    have h3 : sin (-Real.pi) = 0 := by
      have : sin (-Real.pi) = - sin Real.pi := by
        rw [sin_neg]
      rw [this, Real.sin_pi]
      all_goals norm_num
    linarith
  have h3 : cos (2 * (-π + Real.pi / 2)) = -1 := by
    have eq4 : 2 * (-π + Real.pi / 2) = - (Real.pi) := by
      nlinarith [Real.pi_pos]
    rw [eq4]
    have h4 : cos (-Real.pi) = -1 := by
      rw [cos_neg]
      norm_num
    linarith
  have h4 : sin (-π + Real.pi / 2) = -1 := by
    have h5 : -π + Real.pi / 2 = - (Real.pi / 2) := by
      nlinarith [Real.pi_pos]
    rw [h5]
    have h6 : sin (-(Real.pi / 2)) = -1 := by
      have h7 : sin (-(Real.pi / 2)) = - sin (Real.pi / 2) := by
        rw [sin_neg]
      rw [h7]
      rw [Real.sin_pi_div_two]
      all_goals norm_num
    linarith
  have h5 : cos (-π + Real.pi / 2) = 0 := by
    have h6 : -π + Real.pi / 2 = - (Real.pi / 2) := by
      nlinarith [Real.pi_pos]
    rw [h6]
    have h7 : cos (-(Real.pi / 2)) = 0 := by
      have h8 : cos (-(Real.pi / 2)) = cos (Real.pi / 2) := by
        rw [cos_neg]
      rw [h8]
      rw [Real.cos_pi_div_two]
      all_goals norm_num
    linarith
  have h6 : sin (2 * (-π - Real.pi / 2)) = 0 := by
    have eq5 : 2 * (-π - Real.pi / 2) = -3 * Real.pi := by
      nlinarith [Real.pi_pos]
    rw [eq5]
    have : sin (-3 * Real.pi) = 0 := by
      have h3 : sin (-3 * Real.pi) = - sin (3 * Real.pi) := by
        rw [show -3 * Real.pi = - (3 * Real.pi) by ring]
        rw [sin_neg]
      have h4 : sin (3 * Real.pi) = 0 := by
        have : 3 * Real.pi = Real.pi + 2 * Real.pi := by
          nlinarith [Real.pi_pos]
        rw [this]
        rw [sin_add, sin_two_pi, cos_two_pi]
        norm_num
      rw [h3, h4]
      all_goals norm_num
    linarith
  have h8 : cos (2 * (-π - Real.pi / 2)) = -1 := by
    have eq5 : 2 * (-π - Real.pi / 2) = -3 * Real.pi := by
      nlinarith [Real.pi_pos]
    rw [eq5]
    have h9 : cos (-3 * Real.pi) = -1 := by
      have h10 : cos (-3 * Real.pi) = cos (3 * Real.pi) := by
        rw [show -3 * Real.pi = - (3 * Real.pi) by ring]
        rw [cos_neg]
      rw [h10]
      have h11 : cos (3 * Real.pi) = -1 := by
        have : 3 * Real.pi = Real.pi + 2 * Real.pi := by
          nlinarith [Real.pi_pos]
        rw [this]
        rw [cos_add, sin_two_pi, cos_two_pi]
        norm_num
      linarith
    linarith
  have h9 : sin (-π - Real.pi / 2) = 1 := by
    have eq6 : -π - Real.pi / 2 = - (3 * Real.pi / 2) := by
      nlinarith [Real.pi_pos]
    rw [eq6]
    have h7 : sin (-(3 * Real.pi / 2)) = 1 := by
      have h8 : sin (-(3 * Real.pi / 2)) = - sin (3 * Real.pi / 2) := by
        rw [sin_neg]
      rw [h8]
      have h9 : sin (3 * Real.pi / 2) = -1 := by
        have h10 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by
          nlinarith [Real.pi_pos]
        rw [h10]
        have h11 : sin (Real.pi + Real.pi / 2) = -1 := by
          rw [sin_add, Real.sin_pi, Real.cos_pi]
          norm_num [Real.sin_pi_div_two, Real.cos_pi_div_two]
        linarith
      linarith
    linarith
  have h10 : cos (-π - Real.pi / 2) = 0 := by
    have eq7 : -π - Real.pi / 2 = - (3 * Real.pi / 2) := by
      nlinarith [Real.pi_pos]
    rw [eq7]
    have h7 : cos (-(3 * Real.pi / 2)) = 0 := by
      have h8 : cos (-(3 * Real.pi / 2)) = cos (3 * Real.pi / 2) := by
        rw [cos_neg]
      rw [h8]
      have h9 : cos (3 * Real.pi / 2) = 0 := by
        have h10 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by
          nlinarith [Real.pi_pos]
        rw [h10]
        have h11 : cos (Real.pi + Real.pi / 2) = 0 := by
          rw [cos_add, Real.sin_pi, Real.cos_pi]
          norm_num [Real.sin_pi_div_two, Real.cos_pi_div_two]
        linarith
      linarith
    linarith
  rw [h2, h3, h4, h5] at h1
  rw [h6, h8, h9, h10] at h1
  nlinarith