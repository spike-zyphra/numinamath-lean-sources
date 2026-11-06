import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_86819 {f : ℝ → ℝ → ℝ × ℝ}
  (hf : ∀ a, f a = λ t => (sin t, cos (a * t))) :
  ¬ ∃ c, c > 0 ∧ Function.Periodic (f π) c ∧
  {a | ∃ c, c > 0 ∧ Function.Periodic (f a) c} = ℚ := by

  rintro ⟨c, hc_pos, hp, heq⟩

  have h1 := hp 0
  simp [hf] at h1

  have h2 : sin c = 0 := by 
    norm_num at h1
    exact h1.1

  have h3 : cos (π * c) = 1 := by 
    norm_num at h1 
    exact h1.2

  have h4 : c ≠ 0 := by linarith

  -- sin c = 0 gives c = k * π for some integer k
  have hc1 : ∃ k : ℤ, c = ↑k * Real.pi := by 
    rw [sin_eq_zero_iff] at h2
    rcases h2 with ⟨k, hk⟩ 
    refine ⟨k, by linarith⟩ 

  rcases hc1 with ⟨k, hck⟩

  have hk_pos : k > 0 := by 
    by_contra h 
    push_neg at h 
    have : k ≤ 0 := by linarith 
    have hk_eq : (k : ℝ) ≤ (0 : ℝ) := by exact_mod_cast this 
    nlinarith [ show 0 < c by linarith, show 0 < Real.pi by linarith [ Real.pi_pos ] ] 

  -- cos ( π * c ) = 1 
  have h5 : cos (π * c) = 1 := h3 
  rw [ show π * c = ↑k * Real.pi ^ 2 by 
      rw [hck] 
      all_goals ring 
    ] at h5

  -- cos (k * π ^ 2 ) = 1 
  have hc2 : ∃ m : ℤ, (k : ℝ) * Real.pi ^ 2 = 2 * (m : ℝ) * Real.pi := by 
    have h9 : cos (↑k * Real.pi ^ 2) = 1 := h5 
    rw [Real.cos_eq_one_iff] at h9 
    rcases h9 with ⟨m, hm⟩ 
    refine ⟨m, by nlinarith [ Real.pi_pos ]⟩

  rcases hc2 with ⟨m, hcm⟩ 
  have hk_eq : (k : ℝ) * Real.pi = 2 * (m : ℝ) := by 
    have eq1 : (k : ℝ) * Real.pi ^ 2 = 2 * (m : ℝ) * Real.pi := by 
      simpa using hcm 
    have eq2 : Real.pi ≠ 0 := Real.pi_ne_zero 
    have eq3 : (k : ℝ) * Real.pi = 2 * (m : ℝ) := by 
      apply (mul_left_inj' eq2).mp 
      linarith 
    linarith 

  have h6 : (Real.pi : ℝ) = (2 * (m : ℝ) / (k : ℝ) ) := by 
    have hk0 : (k : ℝ) ≠ 0 := by 
      have hk7 : k > 0 := hk_pos 
      have : k ≥ 1 := by omega 
      have : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast this 
      nlinarith 
    field_simp at *
    nlinarith [ hk_eq, Real.pi_pos ]

  have h7 : Irrational Real.pi := by 
    apply irrational_pi 

  -- Show that this implies π is rational, which is a contradiction
  have h8 : ¬ Irrational Real.pi := by 
    rw [h6] 
    simp 

  contradiction