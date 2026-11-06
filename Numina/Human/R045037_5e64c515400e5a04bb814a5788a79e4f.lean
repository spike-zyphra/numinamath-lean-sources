import Mathlib

open Polynomial

/- ## Task A-3.3. (10 points)

Prove that there does not exist a rational number $x$ such that $\left\{x^{2}\right\}+\{x\}=1$.

Find at least one real number $x$ that satisfies this equation.

The notation $\{x\}$ represents the fractional part of $x$, i.e., $\{x\}=x-\lfloor x\rfloor$ where $\lfloor x\rfloor$ is the greatest integer not greater than $x$. For example, $\lfloor 3.4\rfloor=3,\{3.4\}=0.4$. -/
theorem number_theory_240617 : (¬∃ x : ℚ, Int.fract (x ^ 2) + Int.fract x = 1) ∧ ∃ x : ℝ, Int.fract (x ^ 2) + Int.fract x = 1 := by
  constructor
  . -- If rational x satisfies the equation {x ^ 2} + {x} = 1
    rintro ⟨x, hx⟩
    -- We can find an integer z such that x ^ 2 + x - z = 0
    obtain ⟨z, hz⟩ : ∃ z : ℤ, x ^ 2 + x - z = 0 := by
      rcases Int.fract_add (x ^ 2) x with ⟨z, hz⟩
      use z + 1 + ⌊x ^ 2 + x⌋
      simp
      linarith [Int.floor_add_fract (x ^ 2 + x)]
    -- Consider the polynomial X ^ 2 + X - z : ℤ[X]
    -- It is quadratic, monic, and has a root x
    have hp₁ : (X ^ 2 + X - C z).natDegree = 2 := by compute_degree!
    have hp₂ : (X ^ 2 + X - C z).Monic := by
      rw [Monic.def, ← coeff_natDegree, hp₁]
      simp [-eq_intCast, coeff_X]
    have hp₃ : aeval x (X ^ 2 + X - C z) = 0 := by simp [hz]
    -- We have the integral root theorem:
    -- If a monic polynomial with integer coefficients has a rational root, then it is an integer.
    -- Therefore, x must be an integer.
    obtain ⟨n, hn⟩ := isInteger_of_is_root_of_monic hp₂ hp₃
    obtain rfl : n = x := by simpa using hn
    -- So x ^ 2 and x has zero fractional part, contradicting the given equation.
    rw [← Int.cast_pow, Int.fract_intCast, Int.fract_intCast] at hx
    simp at hx
  . -- We set x = (√5 - 1) / 2
    -- We show that x satisfies the equation {x ^ 2} + {x} = 1
    use (√5 - 1) / 2
    -- Give bounds for √5
    have h₁ : 2 < √5 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have h₂ : √5 < 3 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    -- We show that the fractional part of x ^ 2 and x are both themselves
    -- Since they are both in [0, 1)
    have h₃ : Int.fract (((√5 - 1) / 2) ^ 2) = ((√5 - 1) / 2) ^ 2 := by
      rw [Int.fract_eq_self]
      ring_nf
      simp
      constructor <;> linarith
    have h₄ : Int.fract ((√5 - 1) / 2) = ((√5 - 1) / 2) := by
      rw [Int.fract_eq_self]
      constructor <;> linarith
    -- Simple calculation shows that the equation holds
    rw [h₃, h₄]
    ring_nf
    simp
    norm_num
