import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_280129 {f : ℝ → ℝ} (hf : f = λ x => (2 * sin x + 1) / (3 * sin x - 5)) :
    IsLeast {T | 0 < T ∧ f = f ∘ (λ x => x + T)} (2 * π) := by
  constructor
  · -- First, we need to prove that 2 * π is in the set
    constructor
    · -- Show 2 * π > 0
      have h1 : 0 < π := Real.pi_pos
      linarith [h1]
    · -- Show that f = f ∘ (λ x => x + 2 * π)
      funext x
      rw [hf]
      simp [show sin (x + 2 * π) = sin x by rw [sin_add_two_pi]]
  · -- Now, we need to prove that if T is in the set, then T ≥ 2 * π
    intro T ⟨hT_pos, hT_period⟩
    have h1 : ∀ x, f x = f (x + T) := by
      simpa using congr_fun hT_period
    have h2 := h1 (Real.pi / 2)
    rw [hf] at h2
    simp at h2
    have h3 : sin (Real.pi / 2 + T) = cos T := by
      rw [sin_add]
      simp
    rw [h3] at h2
    have h4 : cos T = 1 := by
      have h2' : (2 * cos T + 1) / (3 * cos T - 5) = (-3 / 2 : ℝ) := by
        have h6 : 3 * cos T - 5 ≠ 0 := by
          by_contra h'
          have h6 : 3 * cos T - 5 = 0 := by linarith
          have h7 : cos T = 5 / 3 := by linarith
          have h9 : cos T ^ 2 + sin T ^ 2 = 1 := cos_sq_add_sin_sq T
          nlinarith [sq_nonneg (cos T), sq_nonneg (sin T), h7]
        field_simp [h6] at h2 ⊢
        linarith
      have h5 : cos T = 1 := by
        have h6 : 3 * cos T - 5 ≠ 0 := by
          by_contra h'
          have h6 : 3 * cos T - 5 = 0 := by linarith
          have h7 : cos T = 5 / 3 := by linarith
          have h9 : cos T ^ 2 + sin T ^ 2 = 1 := cos_sq_add_sin_sq T
          nlinarith [sq_nonneg (cos T), sq_nonneg (sin T), h7]
        field_simp [h6] at h2' ⊢
        linarith
      exact h5
    have h5 : ∃ n : ℤ, T = (n : ℝ) * (2 * π) := by
      have hcos : cos T = 1 := h4
      have h6 : ∃ n : ℤ, T = (n : ℝ) * (2 * π) := by
        rw [cos_eq_one_iff] at hcos
        rcases hcos with ⟨n, hn⟩
        use n
        linarith [hn]
      exact h6
    rcases h5 with ⟨n, hn⟩
    have hn_pos : (n : ℝ) > 0 := by
      nlinarith [hT_pos, Real.pi_pos]
    have hn_int_pos : n > 0 := by
      by_contra h
      push_neg at h
      have : (n : ℝ) ≤ (0 : ℝ) := by
        exact_mod_cast show (n : ℤ) ≤ (0 : ℤ) by omega
      nlinarith [Real.pi_pos, hn, hn_pos]
    have hT_ge : T ≥ 2 * π := by
      have hn_nlinarith : (n : ℝ) ≥ (1 : ℝ) := by
        exact_mod_cast show n ≥ (1 : ℤ) by omega
      nlinarith [Real.pi_pos, hn, hn_nlinarith]
    linarith