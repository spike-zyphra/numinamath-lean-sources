import Mathlib

theorem algebra_9228 (φ : ℝ) (hφ : -(Real.pi / 2) < φ ∧ φ < Real.pi / 2)
    (f : ℝ → ℝ) (hf : f = fun x => Real.sin (2 * x + φ))
    (h : IsGreatest (Set.range f) (f (Real.pi / 6))) :
    φ = Real.pi / 6 := by
  have h1 : ∀ x, f x = Real.sin (2 * x + φ) := by
    intro x
    rw [hf]
  have h2 : f (Real.pi / 6) = Real.sin (2 * (Real.pi / 6) + φ) := by
    apply h1
  have h3 : ∀ y ∈ Set.range f, y ≤ f (Real.pi / 6) := by
    rcases h with ⟨h4, h5⟩
    intro y hy
    have : y ≤ f (Real.pi / 6) := by
      apply h5
      exact hy
    assumption
  have h5 : f ((Real.pi / 2 - φ) / 2) ≤ f (Real.pi / 6) := by
    apply h3
    simp [Set.mem_range]
    all_goals try { 
      use (Real.pi / 2 - φ) / 2
      all_goals try { 
        simp [h1]
        <;> linarith 
      } 
    }
  have h6 : f ((Real.pi / 2 - φ) / 2) = 1 := by
    rw [h1]
    have h7 : 2 * ((Real.pi / 2 - φ) / 2) + φ = Real.pi / 2 := by
      ring
    rw [h7]
    norm_num
  have h7 : f (Real.pi / 6) = Real.sin (2 * (Real.pi / 6) + φ) := by
    apply h1
  have h8 : Real.sin (2 * (Real.pi / 6) + φ) ≥ 1 := by
    linarith [h5, h6, h7]
  have h9 : Real.sin (2 * (Real.pi / 6) + φ) ≤ 1 := by
    have h10 : -1 ≤ Real.sin (2 * (Real.pi / 6) + φ) ∧ Real.sin (2 * (Real.pi / 6) + φ) ≤ 1 := by
      apply Real.sin_mem_Icc
    linarith
  have h10 : Real.sin (2 * (Real.pi / 6) + φ) = 1 := by
    linarith [h8, h9]
  have h11 : ∃ k : ℤ, 2 * (Real.pi / 6) + φ = Real.pi / 2 + 2 * Real.pi * k := by
    have h12 : Real.sin (2 * (Real.pi / 6) + φ) = 1 := h10
    obtain ⟨k, hk⟩ := Real.sin_eq_one_iff.1 h12
    use k
    all_goals try { 
      nlinarith
    }
  rcases h11 with ⟨k, hk⟩
  have hk0 : k = 0 := by
    by_contra h
    push_neg at h
    have h12 : k ≥ 1 ∨ k ≤ -1 := by omega
    rcases h12 with (h12 | h12)
    · -- k ≥ 1
      have hk1 : (k : ℝ) ≥ 1 := by exact_mod_cast h12
      have h14 : φ ≥ Real.pi / 2 := by
        nlinarith [show (k : ℝ) ≥ (1 : ℝ) by linarith, Real.pi_pos, Real.pi_pos, Real.pi_pos]
      have h15 : φ < Real.pi / 2 := hφ.right
      linarith
    · -- k ≤ -1
      have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast h12
      have h14 : φ ≤ -Real.pi / 2 := by
        nlinarith [show (k : ℝ) ≤ (-1 : ℝ) by linarith, Real.pi_pos, Real.pi_pos, Real.pi_pos]
      have h15 : -(Real.pi / 2) < φ := hφ.left
      nlinarith
  rw [show (k : ℝ) = (0 : ℝ) by exact_mod_cast hk0] at hk
  have hk' : 2 * (Real.pi / 6) + φ = Real.pi / 2 := by
    nlinarith
  linarith