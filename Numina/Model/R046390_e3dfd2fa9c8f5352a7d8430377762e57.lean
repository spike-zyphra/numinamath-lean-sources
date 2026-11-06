import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9370 {f : ℝ → ℝ} (hf : f = λ x => sqrt 3 * sin x + cos x) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (2 * π) := by
  constructor
  · -- First show that 2*π is in the set
    constructor
    · -- Show 0 < 2 * π
      nlinarith [Real.pi_pos]
    · -- Show $f = \fun x \Rightarrow f (x + 2 * \pi)$
      funext x
      rw [hf]
      have h1 : sqrt 3 * sin x + cos x = sqrt 3 * sin (x + 2 * π) + cos (x + 2 * π) := by
        have h2 : sin (x + 2 * π) = sin x := Real.sin_add_two_pi x
        have h3 : cos (x + 2 * π) = cos x := Real.cos_add_two_pi x
        rw [h2, h3]
        all_goals ring
      simpa using h1
  · -- Now show the minimality
    intro T ⟨htpos, heq⟩
    by_contra h
    push_neg at h
    have eq1 := congr_fun heq 0
    simp [hf] at eq1
    have eq2 := congr_fun heq (Real.pi / 2)
    simp [hf, Real.sin_pi_div_two, Real.cos_pi_div_two, Real.sin_add, Real.cos_add] at eq2
    have h1 : sin T ^ 2 + cos T ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq T
    have heq3 : sin T = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ 3), sq_nonneg (sin T), sq_nonneg (cos T - 1)]
    have heq4 : cos T = 1 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ 3), heq3, sq_nonneg (cos T - 1)]
    -- Derive contradiction from T < 2 * π, sin T = 0, and cos T = 1.
    have heq5 : T < 2 * Real.pi := by
      linarith [show T < 2 * Real.pi by nlinarith [h, Real.pi_pos]]
    -- Derive contradiction from T < 2 * π and sin T = 0 and T > 0
    -- First taken side cases
    by_cases h10 : T < Real.pi
    · -- $T < \pi$, show contradiction.
      have heq30 : sin T > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        all_goals linarith
      linarith
    · -- $T \geq \pi$
      have h30 : T ≥ Real.pi := by linarith
      by_cases h40 : T > Real.pi
      · -- $T > \pi$
        have heq34 : sin T < 0 := by
          have heq32 : Real.pi < T := by linarith
          have heq20 : T < 2 * Real.pi := by linarith
          have heq30 : sin T < 0 := by
            have heq10 : Real.pi < T := heq32
            have heq20 : T < 2 * Real.pi := heq20
            have heq70 : sin T = -sin (T - Real.pi) := by
              rw [show T = T - Real.pi + Real.pi by nlinarith]
              rw [sin_add, sin_pi, cos_pi]
              ring
            have heq80 : sin (T - Real.pi) > 0 := by
              have heq40 : Real.pi < T := heq32
              have heq50 : T - Real.pi > 0 := by linarith
              have heq60 : T - Real.pi < Real.pi := by linarith [Real.pi_pos, show T < 2 * Real.pi by linarith]
              apply sin_pos_of_pos_of_lt_pi
              all_goals linarith
            rw [heq70]
            linarith
          linarith
        linarith
      · -- T ≤ Real.pi
        have heq24 : T = Real.pi := by
          nlinarith
        rw [heq24] at heq4
        have heq30 : cos (Real.pi) = -1 := Real.cos_pi
        rw [heq30] at heq4
        all_goals linarith