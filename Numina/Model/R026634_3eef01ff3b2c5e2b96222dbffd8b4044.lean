import Mathlib

theorem algebra_7008 : ∃x : ℝ, Real.sin x = 4 / 5 ∧ Real.cos x = -3 / 5 := by
  use Real.pi - Real.arcsin (4 / 5)
  constructor
  · -- Show that $\sin(\pi - \arcsin(4/5)) = 4/5$
    have h1 : Real.sin (Real.pi - Real.arcsin (4 / 5)) = 4 / 5 := by
      rw [Real.sin_pi_sub]
      rw [Real.sin_arcsin]
      all_goals norm_num
    linarith [h1]
  · -- Show that $\cos(\pi - \arcsin(4/5)) = -3/5$
    have h2 : Real.cos (Real.pi - Real.arcsin (4 / 5)) = -3 / 5 := by
      rw [Real.cos_pi_sub]
      have h4 : Real.cos (Real.arcsin (4 / 5)) = 3 / 5 := by
        have h : Real.cos (Real.arcsin (4 / 5)) = Real.sqrt (1 - (4 / 5) ^ 2) := by
          rw [Real.cos_arcsin]
          all_goals norm_num
        rw [h]
        have : Real.sqrt (1 - (4 / 5) ^ 2 : ℝ) = 3 / 5 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> norm_num
        rw [this]
        all_goals norm_num
      rw [h4]
      all_goals norm_num
    linarith [h2]
  all_goals norm_num
  <;> try { norm_num [Real.sin_sq] }
  <;> all_goals norm_num
  <;> all_goals norm_num
  <;> all_goals norm_num
  <;> all_goals norm_num