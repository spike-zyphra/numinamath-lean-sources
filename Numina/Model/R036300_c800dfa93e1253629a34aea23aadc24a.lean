import Mathlib

theorem calculus_162156 (f : ℝ → ℝ) (hf : f = fun x => (Real.sin x)^2) :
    deriv (deriv f) = fun x => 2 * Real.cos (2 * x) := by
  have hf1 : deriv f = fun x => 2 * Real.sin x * Real.cos x := by
    funext x 
    rw [hf] 
    simp [deriv_pow, Real.deriv_sin]
    <;> ring_nf <;> field_simp [Real.cos_sq_add_sin_sq] 
    <;> ring 
  rw [hf1]
  funext x 
  have h1 : Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 := by
    rw [show 2 * x = 2 * x by rfl]
    rw [Real.cos_two_mul, Real.sin_sq]
    <;> ring_nf <;> simp [Real.cos_sq_add_sin_sq] 
    <;> ring 
  have eq3 : deriv (fun (y : ℝ) => 2 * Real.sin y * Real.cos y) x = 2 * (Real.cos x ^ 2 - Real.sin x ^ 2) := by
    simp [deriv_mul, deriv_id'', mul_comm]
    <;> ring_nf <;> field_simp [Real.cos_sq, Real.sin_sq]
    <;> ring_nf <;> norm_num 
    all_goals try tauto 
  have eq4 : deriv (fun (y : ℝ) => 2 * Real.sin y * Real.cos y) x = 2 * Real.cos (2 * x) := by
    have eq5 : deriv (fun (y : ℝ) => 2 * Real.sin y * Real.cos y) x = 2 * (Real.cos x ^ 2 - Real.sin x ^ 2) := eq3
    have eq6 : Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 := h1 
    calc 
      deriv (fun (y : ℝ) => 2 * Real.sin y * Real.cos y) x = 2 * (Real.cos x ^ 2 - Real.sin x ^ 2) := eq5
      _ = 2 * (Real.cos (2 * x)) := by 
        rw [show Real.cos x ^ 2 - Real.sin x ^ 2 = Real.cos (2 * x) by 
          linarith [eq6]
        ]
        <;> all_goals ring_nf 
      _ = 2 * Real.cos (2 * x) := by ring
  simpa using eq4 
  all_goals try tauto 
  all_goals try tauto