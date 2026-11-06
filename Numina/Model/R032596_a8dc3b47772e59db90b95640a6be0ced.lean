import Mathlib

theorem algebra_9291 {φ : ℝ} (hφ : φ ∈ Set.Icc 0 Real.pi) :
(∀ x, (fun x => Real.sin (x + φ)) (-x)=(fun x => Real.sin (x + φ)) x) ↔ φ = Real.pi / 2 := by
  rcases hφ with ⟨hφ1, hφ2⟩
  constructor
  · -- Forward: if y=sin(x+φ) is even, then φ=π/2
    intro heven
    have h1 := heven (Real.pi / 2)
    have eq1 : Real.sin (- (Real.pi / 2) + φ) = Real.sin (Real.pi / 2 + φ) := by 
      simpa using h1
    have eq2 : Real.sin (- (Real.pi / 2) + φ) = - Real.cos φ := by 
      have h2 : - (Real.pi / 2) + φ = φ - (Real.pi / 2) := by ring 
      rw [h2]
      rw [Real.sin_sub]
      simp [Real.sin_pi_div_two, Real.cos_pi_div_two]
    have eq3 : Real.sin (Real.pi / 2 + φ) = Real.cos φ := by 
      rw [Real.sin_add]
      simp [Real.sin_pi_div_two, Real.cos_pi_div_two]
    rw [eq2, eq3] at eq1
    have h2 : Real.cos φ = 0 := by 
      nlinarith [eq1]
    have h3 : φ = Real.pi / 2 := by
      apply Real.cos_eq_zero_iff.1 at h2
      rcases h2 with ⟨k, hk⟩
      have hk1 : k = 0 := by
        by_cases h4 : k > 0
        · -- k ≥ 1
          have hk2 : k ≥ 1 := by omega 
          have h5 : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast hk2 
          nlinarith [Real.pi_pos, Real.pi_gt_three]
        · -- k ≤ 0 
          by_cases h6 : k < 0
          · -- k ≤ -1 
            have hk3 : k ≤ -1 := by omega 
            have h7 : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hk3 
            nlinarith [Real.pi_pos, Real.pi_gt_three]
          · -- k = 0 
            omega 
      rw [hk, show (k : ℝ) = (0 : ℝ) by exact_mod_cast hk1] 
      nlinarith [Real.pi_pos, Real.pi_gt_three]
    exact h3 
  · -- Backward: if φ=π/2, then y=sin(x+φ) is even
    intro heq
    intro x
    have h4 : φ = Real.pi / 2 := by linarith [heq]
    simp [h4]
    have eq1 : Real.sin ((-x) + Real.pi / 2) = Real.cos x := by
      have h6 : Real.sin ((-x) + Real.pi / 2) = Real.sin (Real.pi / 2 - x) := by 
        ring_nf 
      rw [h6]
      have h7 : Real.sin (Real.pi / 2 - x) = Real.cos x := by 
        rw [Real.sin_pi_div_two_sub]
      rw [h7]
    have eq2 : Real.sin (x + Real.pi / 2) = Real.cos x := by 
      have h6 : Real.sin (x + Real.pi / 2) = Real.sin x * Real.cos (Real.pi / 2) + Real.cos x * Real.sin (Real.pi / 2) := by 
        rw [Real.sin_add]
      rw [h6]
      have h7 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
      have h8 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
      simp [h7, h8]
    linarith [eq1, eq2]