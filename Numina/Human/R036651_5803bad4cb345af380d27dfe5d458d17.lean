import Mathlib

open Finset BigOperators

/-Let f(x)=x^3+a*x+b, with a ≠ b, and suppose the tangent lines to the graph of f at x=a and x=b are parallel. Find f(1)-/
theorem Algebra_611313 (a b:ℝ ) (hab : a - b ≠ 0) (hf : deriv (λ x:ℝ ↦ x^3+a*x+b) a = deriv (λ x:ℝ ↦ x^3+a*x+b) b) : (λ x:ℝ ↦ x^3+a*x+b) 1 = 1 :=by{
  -- First we cauculate the deriv of f.
  have key: ∀ x, deriv (λ x:ℝ ↦ x^3+a*x+b) x = 3*x^2 + a:=by{
    intro x
    have h1_deriv : deriv (λ x:ℝ ↦ x^3+a*x) x = deriv (λ x ↦  x^3) x + deriv (λ x↦  a * x) x  :=by{
      refine deriv_add ?hf ?hg
      exact differentiableAt_pow 3
      apply DifferentiableAt.const_mul
      exact differentiableAt_id'
    }
    have h2_deriv : deriv (λ x:ℝ ↦ x^3+a*x+b) x = deriv (λ x ↦  x^3+a*x) x + deriv (λ x↦  b) x :=by{
      rw [deriv_add]
      refine DifferentiableAt.add ?hf.hf ?hf.hg
      exact differentiableAt_pow 3
      apply DifferentiableAt.const_mul
      exact differentiableAt_id'
      exact differentiableAt_const b
    }
    rw [h1_deriv] at h2_deriv
    rw [h2_deriv]
    have h1 : deriv (λ x↦  x^3) x = 3 * x^2:=by{
      rw [deriv_pow' 3]
      simp
    }
    have h2 : deriv (λ x↦  a * x) x = a:=by{
      rw [deriv_const_mul a]
      have hid_deriv:deriv (λ x↦  x) x = 1:=by{
        apply deriv_id
      }
      rw [hid_deriv]
      simp
      exact differentiableAt_id'
    }
    have h3 : deriv (λ x↦  b) x = 0:=by{
      apply deriv_const
    }
    rw [h1, h2, h3]
    simp
  }
  -- Then we use the fact that f'(a)=f'(b).
  have h_eq : 3 * a^2 + a = 3 * b^2 + a:=by{
    rw [← key, ← key]
    exact hf
  }
  have h_mul_eq_zero : (a-b)*(a+b)=0:=by{
    linarith
  }
  have ha_add_b: a+b=0:=by{
    apply mul_eq_zero.mp at h_mul_eq_zero
    cases h_mul_eq_zero
    tauto
    tauto
  }
  calc (λ x:ℝ ↦ x^3+a*x+b) 1 = a+b+1:=by{
    simp
    ring
  }
  -- Finally we compute f(1).
   _ = 0+1:=by rw[ha_add_b]
   _ = 1:=by simp
}