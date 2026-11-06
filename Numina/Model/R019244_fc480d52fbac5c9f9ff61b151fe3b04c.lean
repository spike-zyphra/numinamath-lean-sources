import Mathlib

open BigOperators Real Set

theorem algebra_217016 {f : ℝ → ℝ}
  (hf : f = λ x => 4 * sin (3 * x + π / 4) + 3 * cos (3 * x + π / 4)) :
  IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (2 * π / 3) := by
  constructor
  · -- Show that 2π/3 is in the set
    constructor
    · -- Show 2π/3 > 0
      positivity
    · -- Show f = fun x ↦ f (x + 2 * π / 3)
      funext x
      have eq1 : f x = 4 * sin (3 * x + π / 4) + 3 * cos (3 * x + π / 4) := by simp [hf]
      have eq2 : f (x + 2 * π / 3) = 4 * sin (3 * (x + 2 * π / 3) + π / 4) + 3 * cos (3 * (x + 2 * π / 3) + π / 4) := by simp [hf]
      rw [eq1, eq2]
      have h1 : 3 * (x + 2 * π / 3) + π / 4 = 3 * x + π / 4 + 2 * π := by
        ring_nf
      have h2 : sin (3 * (x + 2 * π / 3) + π / 4) = sin (3 * x + π / 4) := by
        rw [h1]
        have : sin (3 * x + π / 4 + 2 * π) = sin (3 * x + π / 4) := by
          rw [sin_add_two_pi]
        linarith
      have h3 : cos (3 * (x + 2 * π / 3) + π / 4) = cos (3 * x + π / 4) := by
        rw [h1]
        have : cos (3 * x + π / 4 + 2 * π) = cos (3 * x + π / 4) := by
          rw [cos_add_two_pi]
        linarith
      simp [h2, h3]
  · -- Show that 2π/3 is the smallest such positive period
    intro T ⟨hT_pos, hT_period⟩
    by_contra h
    push_neg at h
    have eq1 : f = λ x => f (x + T) := by
      exact hT_period
    have eq2 := congr_fun eq1 (Real.pi / 12)
    have eq3 := congr_fun eq1 (-Real.pi / 12)
    have eq4 : f (Real.pi / 12) = 4 * sin (3 * (Real.pi / 12) + Real.pi / 4) + 3 * cos (3 * (Real.pi / 12) + Real.pi / 4) := by simp [hf]
    have eq5 : f (-Real.pi / 12) = 4 * sin (3 * (-Real.pi / 12) + Real.pi / 4) + 3 * cos (3 * (-Real.pi / 12) + Real.pi / 4) := by simp [hf]
    have eq6 : f (Real.pi / 12 + T) = 4 * sin (3 * (Real.pi / 12 + T) + Real.pi / 4) + 3 * cos (3 * (Real.pi / 12 + T) + Real.pi / 4) := by simp [hf]
    have eq7 : f (-Real.pi / 12 + T) = 4 * sin (3 * (-Real.pi / 12 + T) + Real.pi / 4) + 3 * cos (3 * (-Real.pi / 12 + T) + Real.pi / 4) := by simp [hf]
    rw [eq4] at eq2
    rw [eq6] at eq2
    rw [eq5] at eq3
    rw [eq7] at eq3
    have eq8 : 3 * (Real.pi / 12) + Real.pi / 4 = Real.pi / 2 := by
      ring_nf
    have eq9 : 3 * (-Real.pi / 12) + Real.pi / 4 = (0 : ℝ) := by
      ring_nf
    have eq10 : 3 * (Real.pi / 12 + T) + Real.pi / 4 = Real.pi / 2 + 3 * T := by
      ring_nf
    have eq11 : 3 * (-Real.pi / 12 + T) + Real.pi / 4 = (3 * T : ℝ) := by
      ring_nf
    rw [eq8] at eq2
    rw [eq10] at eq2
    rw [eq9] at eq3
    rw [eq11] at eq3
    have eq12 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have eq13 : cos (Real.pi / 2) = 0 := by
      rw [Real.cos_pi_div_two]
    have eq14 : sin (Real.pi / 2 + 3 * T) = cos (3 * T) := by
      rw [sin_add, sin_pi_div_two, cos_pi_div_two]
      ring_nf
    have eq15 : cos (Real.pi / 2 + 3 * T) = -sin (3 * T) := by
      rw [cos_add, sin_pi_div_two, cos_pi_div_two]
      ring_nf
    simp [eq12, eq13, eq14, eq15] at eq2
    have eq16 : sin (0 : ℝ) = 0 := by
      simp
    have eq17 : cos (0 : ℝ) = 1 := by
      simp
    simp [eq16, eq17] at eq3
    have eq20 : sin (3 * T) = 0 := by
      nlinarith [sq_nonneg (sin (3 * T) : ℝ), sq_nonneg (cos (3 * T) : ℝ), Real.sin_sq_add_cos_sq (3 * T)]
    have eq21 : cos (3 * T) = 1  := by
      nlinarith [sq_nonneg (sin (3 * T) : ℝ), sq_nonneg (cos (3 * T) : ℝ), Real.sin_sq_add_cos_sq (3 * T)]
    have eq22 : ∃ k : ℤ, 3 * T = 2 * Real.pi * (k : ℝ) := by
      have h1 : sin (3 * T) = 0  := eq20
      have h2 : cos (3 * T) = 1  := eq21
      have h3 : ∃ k : ℤ, 3 * T = 2 * Real.pi * (k : ℝ) := by
        have h4 : cos (3 * T) = 1  := h2
        rw [Real.cos_eq_one_iff] at h4
        obtain ⟨k, hk⟩ := h4
        use k
        all_goals
          try linarith [Real.pi_pos]
      exact h3
    rcases eq22 with ⟨k, hk⟩
    have hkpos : k > 0  := by
      by_contra h
      push_neg at h
      have hknonpos : k ≤ 0  := by linarith
      have hTnonpos : (k : ℝ) ≤ 0  := by
        exact_mod_cast hknonpos
      have hTle0 : 3 * T ≤ 0  := by
        nlinarith [Real.pi_pos, hTnonpos]
      have hT_pos' : 3 * T > 0  := by
        nlinarith [show T > 0 by linarith [hT_pos]]
      linarith
    have hkge1 : k ≥ 1  := by
      omega
    have hk1 : (k : ℝ) ≥ (1 : ℝ)  := by
      exact_mod_cast hkge1
    have hk2 : 3 * T ≥ 2 * Real.pi  := by
      nlinarith [Real.pi_pos, hk1, hk]
    have hk3 : T ≥ 2 * Real.pi / 3  := by
      linarith
    linarith