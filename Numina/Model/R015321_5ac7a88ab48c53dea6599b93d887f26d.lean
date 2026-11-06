import Mathlib

open BigOperators Real Set

lemma lemma_1 (x : ℝ) :
  sin x ^ 6 + cos x ^ 6 = 1 - 3 * sin x ^ 2 * cos x ^ 2 := by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h2 : sin x ^ 6 + cos x ^ 6 = 1 - 3 * sin x ^ 2 * cos x ^ 2 := by
    have h3 : sin x ^ 6 + cos x ^ 6 = (sin x ^ 2 + cos x ^ 2) ^ 3 - 3 * (sin x ^ 2 + cos x ^ 2) * (sin x ^ 2 * cos x ^ 2) := by
      ring
    rw [h3, h1]
    all_goals ring
  linarith [h2]


theorem algebra_252240 (k : ℝ) :
  (∃ c, ∀ x : ℝ, sin x ^ 6 + cos x ^ 6 + k * (sin x ^ 4 + cos x ^ 4) = c) ↔
  k = -3 / 2 := by
  constructor
  · -- Forward direction: if the expression is constant for all x, then k = -3/2.
    intro h
    rcases h with ⟨c, hc⟩
    have eq1 := hc 0
    have eq2 := hc (Real.pi / 2)
    have eq3 := hc (Real.pi / 4)
    have eq1' : sin (0 : ℝ) = 0 := by simp
    have eq1'' : cos (0 : ℝ) = 1 := by simp
    simp [eq1', eq1''] at eq1
    have eq2' : sin (Real.pi / 2 : ℝ) = 1 := by
      rw [sin_pi_div_two]
    have eq2'' : cos (Real.pi / 2 : ℝ) = 0 := by
      rw [cos_pi_div_two]
    simp [eq2', eq2''] at eq2
    have eq3' : sin (Real.pi / 4 : ℝ) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have eq3'' : cos (Real.pi / 4 : ℝ) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    simp [eq3', eq3''] at eq3
    have eq4 : c = 1 + k := by
      nlinarith
    have eq5 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have eq6 : (Real.sqrt 2 / 2 : ℝ) ^ 4 = (1 / 4 : ℝ) := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 4 = ((Real.sqrt 2 / 2 : ℝ) ^ 2) ^ 2 := by ring
        _ = (1 / 2) ^ 2 := by rw [eq5]
        _ = (1 / 4 : ℝ) := by norm_num
    have eq7 : (Real.sqrt 2 / 2 : ℝ) ^ 6 = (1 / 8 : ℝ) := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 6 = ((Real.sqrt 2 / 2 : ℝ) ^ 2) ^ 3 := by ring
        _ = (1 / 2) ^ 3 := by rw [eq5]
        _ = (1 / 8 : ℝ) := by norm_num
    nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (k + 3 / 2)]
  · -- Backward direction: if k = -3/2, then the expression is constant.
    intro hk
    use -1 / 2
    intro x
    have hk' : k = -3 / 2 := hk
    have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h2 : sin x ^ 4 + cos x ^ 4 = 1 - 2 * sin x ^ 2 * cos x ^ 2 := by
      have h1' : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      have h3 : sin x ^ 4 + cos x ^ 4 = (sin x ^ 2 + cos x ^ 2) ^ 2 - 2 * (sin x ^ 2 * cos x ^ 2) := by
        ring
      rw [h3, h1']
      all_goals ring_nf
    have h3 : sin x ^ 6 + cos x ^ 6 = 1 - 3 * sin x ^ 2 * cos x ^ 2 := by
      have h1' : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      have h4 : sin x ^ 6 + cos x ^ 6 = (sin x ^ 2 + cos x ^ 2) ^ 3 - 3 * (sin x ^ 2 + cos x ^ 2) * (sin x ^ 2 * cos x ^ 2) := by
        ring
      rw [h4, h1']
      all_goals ring_nf
    rw [h3, h2, hk']
    nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x ^ 2 - 1 / 2), sq_nonneg (cos x ^ 2 - 1 / 2), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - cos x ^ 2)]