import Mathlib

open Real

theorem calculus_187133 {x1 x2 : ℝ → ℝ}
    (hx1 : x1 = fun t => -1 / t ^ 2) (hx2 : x2 = fun t => -t * log t) :
    DifferentiableOn ℝ x1 (Set.Ioi 0) ∧ DifferentiableOn ℝ x2 (Set.Ioi 0) ∧
    ∀ t ∈ Set.Ioi 0, deriv x1 t = 2 * t * (x1 t) ^ 2 ∧ deriv x2 t = (x2 t) / t - 1 := by
  constructor
  · -- Show that x1 is differentiable on (0, +∞)
    rw [hx1]
    apply DifferentiableOn.div
    · -- Show that -1 is differentiable
      apply differentiableOn_const
    · -- Show that t ^ 2 is differentiable
      apply DifferentiableOn.pow
      apply differentiableOn_id
      all_goals norm_num
    · -- Show that t ^ 2 is non-zero on (0, +∞)
      intro t ht
      have ht' : t > 0 := by simpa using ht
      positivity
  constructor
  · -- Show that x2 is differentiable on (0, +∞)
    rw [hx2]
    apply DifferentiableOn.mul
    · -- Show that (-t : ℝ → ℝ) is differentiable
      apply DifferentiableOn.neg
      apply differentiableOn_id
    · -- Show that (log t : ℝ → ℝ) is differentiable
      apply DifferentiableOn.log
      · -- Show that (t : ℝ → ℝ) is differentiable
        apply differentiableOn_id
      all_goals -- process all positivity goals for log
        try { 
          intro t ht 
          have ht' : t > 0 := by simpa using ht 
          positivity 
        }
      all_goals try { 
        try { 
          intro t ht 
          have ht' : t > 0 := by simpa using ht 
          positivity 
        }
        try { 
          intro t ht 
          have ht' : t > 0 := by simpa using ht 
          positivity 
        }
      }
    all_goals -- other subgoals from the differentiability proof, e.g. from `apply DifferentiableOn.neg` and `apply differentiableOn_id`
      try { try norm_num; try { tauto } }
      try { try { nlinarith } }
  · -- Show that ∀ t ∈ Set.Ioi (0 : ℝ), deriv x1 t = 2 * t * (x1 t) ^ 2 ∧ deriv x2 t = (x2 t) / t - 1
    intro t ht
    have ht' : t > 0 := by simpa using ht
    have h1 : t ≠ 0 := by linarith
    constructor
    · -- Show derivative of x1
      rw [hx1]
      simp [deriv_div, deriv_const, deriv_pow, deriv_id'', pow_two, div_eq_mul_inv, mul_comm]
      all_goals -- goals from `deriv_div` might need `t ≠ 0`, `t^2 ≠ 0`
        try { 
          have ht' : t > 0 := by simpa using ht 
          have h1 : t ≠ 0 := by linarith
          field_simp [h1]
          <;> ring_nf <;> field_simp [h1] <;> nlinarith <;> tauto
        }
    · -- Show derivative of x2
      rw [hx2]
      simp [deriv_mul, deriv_id'', deriv_log, mul_comm]
      all_goals -- goals might need `t ≠ 0` and `t > 0`
        try { 
          have h1' : (t) ≠ (0 : ℝ) := by linarith
          field_simp [h1']
          <;> ring_nf <;> field_simp [h1'] <;> nlinarith <;> tauto
        }