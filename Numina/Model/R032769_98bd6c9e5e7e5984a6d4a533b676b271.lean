import Mathlib

open Real Set

theorem algebra_9165 {f : ℝ → ℝ} (hf : f = λ x => cos (π / 2 - x)) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (2 * π) := by
  have h1 : ∀ x, f x = sin x := by
    intro x
    rw [hf]
    have h : cos (π / 2 - x) = sin x := by 
      rw [cos_pi_div_two_sub]
    simp [h]
  constructor
  · -- Show that $2\pi$ belongs to the set
    constructor
    · -- Show that $2\pi > 0$
      nlinarith [Real.pi_pos]
    · -- Show that $f = \lambda x \Rightarrow f (x + 2\pi)$
      funext x
      rw [h1 x, h1 (x + 2 * Real.pi)]
      simp [Real.sin_add_two_pi]
  · -- Show that $2\pi$ is the least element in the set
    intro T ⟨hT_pos, h_eq⟩
    by_contra h
    push_neg at h
    have eq1 : ∀ x : ℝ, f x = f (x + T) := by
      intro x
      simpa using congr_fun h_eq x
    have eq2 := eq1 (Real.pi / 2)
    have eq3 : f (Real.pi / 2) = 1 := by
      rw [h1]
      norm_num
      <;> try linarith [Real.sin_pi_div_two]
    have eq4 : f (Real.pi / 2 + T) = Real.cos T := by
      rw [h1 (Real.pi / 2 + T)]
      have h2 : sin (Real.pi / 2 + T) = Real.cos T := by 
        rw [sin_add]
        simp [Real.sin_pi_div_two, Real.cos_pi_div_two]
        <;> try ring 
      simpa using h2 
    have eq5 : f (Real.pi / 2) = f (Real.pi / 2 + T) := by
      simpa using eq2
    rw [eq3] at eq5 
    rw [eq4] at eq5 
    have h3 : Real.cos T = 1 := by 
      linarith 
    have h4 : ∃ k : ℤ, T = (k : ℝ) * (2 * Real.pi) := by
      have h5 : Real.cos T = 1 := h3
      have h5' : ∃ k : ℤ, T = (k : ℝ) * (2 * Real.pi) := by
        rw [Real.cos_eq_one_iff] at h5
        rcases h5 with ⟨k, hk⟩ 
        use k 
        <;> nlinarith
      exact_mod_cast h5'
    rcases h4 with ⟨k, hk⟩ 
    have hk2 : k > 0 := by
      by_contra h
      push_neg at h
      have : k ≤ 0 := by omega
      have h7 : (k : ℝ) ≤ (0 : ℝ) := by exact_mod_cast this 
      nlinarith [Real.pi_pos, mul_pos Real.pi_pos (show (0 : ℝ) < 2 by norm_num)]
    have hk3 : k < 1 := by 
      by_contra h
      push_neg at h
      have : k ≥ 1 := by omega
      have h8 : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast this 
      nlinarith [Real.pi_pos, mul_pos Real.pi_pos (show (0 : ℝ) < 2 by norm_num)]
    omega