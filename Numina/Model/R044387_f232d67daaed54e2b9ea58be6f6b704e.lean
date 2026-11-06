import Mathlib

open MvPolynomial

theorem calculus_717 {k : ℕ} (hk : 0 < k) (M N : MvPolynomial (Fin 2) ℝ)
    (hMN : M.totalDegree = k ∧ N.totalDegree = k) :
    ∃ F : MvPolynomial (Fin 2) ℝ, F.totalDegree = k ∧
      ∀ x y : ℝ, x * deriv (fun x => MvPolynomial.eval (fun n => if n = 0 then x else y) F) x +
        y * deriv (fun y => MvPolynomial.eval (fun n => if n = 0 then x else y) F) y =
      k * MvPolynomial.eval (fun n => if n = 0 then x else y) F := by 
  use (MvPolynomial.X 1) ^ k  -- polynomial y^k
  constructor
  · -- Show that F has total degree k 
    simp [MvPolynomial.totalDegree_pow, MvPolynomial.totalDegree_X]
    all_goals try linarith
  · -- Show that the PDE is satisfied
    intro x y
    simp [deriv_pow, MvPolynomial.eval_pow, MvPolynomial.eval_X]
    all_goals try { 
      cases k with 
      | zero => linarith
      | succ k => 
        simp [pow_succ, pow_zero, mul_add, add_mul, pow_succ, pow_zero, mul_assoc]
        <;> ring_nf
        <;> field_simp
        <;> ring
    }
    all_goals try { 
      cases k with 
      | zero => linarith
      | succ k => 
        simp [pow_succ, pow_zero, mul_add, add_mul, pow_succ, pow_zero, mul_assoc, Nat.succ]
        <;> ring_nf 
        <;> field_simp 
        <;> ring 
    }
    all_goals try { 
      cases k with 
      | zero => linarith
      | succ k => 
        simp [pow_succ, pow_zero, mul_add, add_mul, pow_succ, pow_zero, mul_assoc]
        <;> ring_nf 
        <;> field_simp 
        <;> ring 
    }
    all_goals try { 
      cases k with 
      | zero => linarith
      | succ k => 
        simp [pow_succ, pow_zero, mul_add, add_mul, pow_succ, pow_zero, mul_assoc, Nat.succ]
        <;> ring_nf 
        <;> field_simp 
        <;> ring 
    }
    all_goals try { 
      ring_nf 
      <;> field_simp 
      <;> ring 
    }
    all_goals try { 
      ring_nf 
      <;> field_simp 
      <;> ring 
    }
    all_goals try { 
      ring_nf <;> field_simp 
    }
    all_goals try { 
      ring_nf <;> field_simp 
    }
    all_goals try { 
      nlinarith 
    }
    all_goals try { 
      nlinarith 
    }
    all_goals try { 
      nlinarith 
      <;> tauto 
    }
    all_goals try { 
      nlinarith 
      <;> tauto 
    }
    all_goals try { 
      nlinarith 
      <;> tauto 
    }
    all_goals try { 
      nlinarith <;> tauto <;> tauto <;> tauto
    }
    all_goals try { 
      nlinarith <;> tauto <;> tauto <;> tauto
    }
    all_goals try { ring }
    all_goals try { ring }
    all_goals try { nlinarith }