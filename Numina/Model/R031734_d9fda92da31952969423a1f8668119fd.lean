import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_276977 {f : ℝ → ℝ} (hf : f = λ x => sin x ^ 2) :
    IsLeast {T | 0 < T ∧ ∀ x, f (x + T) = f x} (Real.pi) := by
  constructor
  · -- First, we show π is a positive period of f(x) = sin x ^ 2.
    constructor
    · -- Show π is positive.
      exact Real.pi_pos
    · -- Show f(x + π) = f(x) for all x.
      intro x
      rw [hf]
      have h1 : sin (x + Real.pi) = -sin x := by
        rw [sin_add_pi]
      simp [h1]
      <;> nlinarith [Real.sin_sq_add_cos_sq x]
  · -- Now we need to show minimality: if T is a positive period, then π ≤ T.
    intro T ⟨hTpos, hTperiod⟩
    have h1 := hTperiod (Real.pi / 2 - T)
    have h3 : f (Real.pi / 2 - T + T) = f (Real.pi / 2 - T) := by
      apply hTperiod
    have h3' : f (Real.pi / 2 - T + T) = f (Real.pi / 2) := by
      have h4 : Real.pi / 2 - T + T = Real.pi / 2 := by 
        ring
      rw [h4]
    rw [h3'] at h3
    rw [hf] at h3
    simp at h3
    -- We have $\sin^2(\frac{\pi/2}) = \sin^2(\frac{\pi/2 - T})$ which means $1 = \cos^2 T$.
    have h3 : (Real.cos T) ^ 2 = 1 := by
      have h4 : sin (Real.pi / 2) = 1 := by
        exact sin_pi_div_two
      have h5 : sin (Real.pi / 2 - T) = Real.cos T := by
        have h6 : sin (Real.pi / 2 - T) = Real.cos T := by
          rw [sin_pi_div_two_sub]
        exact h6
      have h7 : sin (Real.pi / 2) ^ 2 = 1 := by
        rw [h4]
        all_goals norm_num
      have h8 : sin (Real.pi / 2 - T) ^ 2 = Real.cos T ^ 2 := by
        rw [h5]
        <;> nlinarith
      nlinarith
    have h4 : Real.cos T ^ 2 = 1 := h3
    have h5 : Real.cos T = 1 ∨ Real.cos T = -1 := by 
      rw [sq_eq_one_iff] at h4
      exact h4
    rcases h5 with (h5 | h5)
    · -- Assume cos T = 1
      by_contra h
      push_neg at h
      have h6 : T < Real.pi := by
        linarith [h]
      have h7 : Real.cos T < 1 := by
        have h8 : Real.cos T < Real.cos (0 : ℝ) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [hTpos, h6, Real.pi_gt_three]
        have h9 : Real.cos (0 : ℝ) = 1 := by
          simp
        nlinarith
      nlinarith [h5, h7]
    · -- Assume cos T = -1
      by_contra h
      push_neg at h
      have h6 : T < Real.pi := by
        linarith [h]
      have h7 : Real.cos T > -1 := by
        have h8 : Real.cos T > Real.cos (Real.pi) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [hTpos, h6, Real.pi_gt_three]
        have h9 : Real.cos (Real.pi) = -1 := by
          exact cos_pi
        nlinarith
      nlinarith [h5, h7]