import Mathlib

open Real

theorem calculus_177945 (y : ℝ → ℝ) (hy : Differentiable ℝ y)
    (h : ∀ x, (y x)^2 + x^2 - 1 = 0) :
    deriv y = fun x => -x / y x := by
  -- By taking derivative of both sides, we get following equation for all x
  have eq2 : ∀ x, deriv (fun (x : ℝ) => (y x) ^ 2 + x ^ 2 - 1) x = 0 := by
    intro x
    have h1 : (fun (x : ℝ) => (y x) ^ 2 + x ^ 2 - 1) = fun (x : ℝ) => (0 : ℝ) := by
      funext x
      specialize h x
      linarith
    simp [h1]
  -- Computing the derivative correctly
  have eq3 : ∀ x, deriv (fun (x : ℝ) => (y x) ^ 2 + x ^ 2 - 1) x = 2 * (y x) * (deriv y x) + 2 * x := by
    intro x
    have h1 : DifferentiableAt ℝ y x := hy.differentiableAt
    have eq1 : deriv (fun (x : ℝ) => (y x) ^ 2 + x ^ 2 - 1) x = 2 * (y x : ℝ) * deriv y x + 2 * x := by
      simp [deriv_add, deriv_sub, deriv_pow, deriv_const, mul_comm, deriv_id'']
      <;> ring_nf 
      <;> try { 
        field_simp [h1, differentiableAt_id]
        <;> ring_nf <;> norm_num
        <;> try {nlinarith}
      }
      <;> try { 
        have h2 : DifferentiableAt ℝ (fun (x : ℝ) => y x ^ 2 + x ^ 2 - 1) x := by
          apply DifferentiableAt.sub
          · -- Show DifferentiableAt ℝ (fun x => y x ^ 2 + x ^ 2) x
            apply DifferentiableAt.add
            · -- Show DifferentiableAt ℝ (fun x => y x ^ 2) x
              apply DifferentiableAt.pow
              exact h1
            · -- Show DifferentiableAt ℝ (fun x => x ^ 2) x
              apply DifferentiableAt.pow
              apply differentiableAt_id
          · -- Show DifferentiableAt ℝ (fun x => (1 : ℝ)) x
            apply differentiableAt_const
        simp [h2] 
      }
      <;> try { 
        exfalso 
        <;> try { 
          have h2 : DifferentiableAt ℝ (fun (x : ℝ) => y x ^ 2 + x ^ 2 - 1) x := by
            apply DifferentiableAt.sub
            · -- Show DifferentiableAt ℝ (fun x => y x ^ 2 + x ^ 2) x
              apply DifferentiableAt.add
              · -- Show DifferentiableAt ℝ (fun x => y x ^ 2) x
                apply DifferentiableAt.pow
                exact h1
              · -- Show DifferentiableAt ℝ (fun x => x ^ 2) x
                apply DifferentiableAt.pow
                apply differentiableAt_id
            · -- Show DifferentiableAt ℝ (fun x => (1 : ℝ)) x
              apply differentiableAt_const
          simp [h2] 
        }
      }
      <;> try { tauto }
      <;> try { 
        exfalso
        <;> try { 
          have h2 : DifferentiableAt ℝ (fun (x : ℝ) => y x ^ 2 + x ^ 2 - 1) x := by
            apply DifferentiableAt.sub
            · -- Show DifferentiableAt ℝ (fun x => y x ^ 2 + x ^ 2) x
              apply DifferentiableAt.add
              · -- Show DifferentiableAt ℝ (fun x => y x ^ 2) x
                apply DifferentiableAt.pow
                exact h1
              · -- Show DifferentiableAt ℝ (fun x => x ^ 2) x
                apply DifferentiableAt.pow
                apply differentiableAt_id
            · -- Show DifferentiableAt ℝ (fun x => (1 : ℝ)) x
              apply differentiableAt_const
          simp [h2] 
        }
      }
    exact eq1
  -- For all x, we then derive 2 * (y x) * deriv y x + 2 * x = 0
  have eq4 : ∀ x, 2 * (y x) * (deriv y x) + 2 * x = 0 := by
    intro x
    have eq5 := eq2 x
    have eq6 := eq3 x
    linarith [eq5, eq6]
  
  funext x
  have eq5 := eq4 x
  -- Show that y x ≠ 0
  have h4 : y x ≠ 0 := by
    by_contra h6
    have : 2 * x = 0 := by
      rw [h6] at eq5
      nlinarith
    have hx0 : x = 0 := by linarith
    have hy0_sq_eq1 : (y 0) ^ 2 + (0 : ℝ) ^ 2 - 1 = 0 := h 0
    have hy0_sq : (y 0) ^ 2 = 1 := by linarith
    have y0_neq_zero : y 0 ≠ 0 := by
      intro hy0_is_zero
      rw [hy0_is_zero] at hy0_sq
      nlinarith
    have h7 : y 0 = 0 := by
      rw [show x = 0 by linarith] at h6
      exact h6
    contradiction
  
  -- Solving for deriv y x
  have eq8 : deriv y x = -x / (y x) := by
    have : 2 * (y x) * (deriv y x) + 2 * x = 0 := eq5
    have eq7 : deriv y x = -x / (y x) := by
      field_simp [h4] at this ⊢
      <;> nlinarith <;> try { tauto } <;> try { linarith }
      <;> try { 
        exfalso
        <;> try { 
          have h9 : y x = 0 := by
            nlinarith
          contradiction
        }
      }
    exact eq7
  exact eq8