import Mathlib

open Polynomial

/- Find constants $A,$ $B,$ $C,$ and $d$ such that
\[\frac{4x^3 - 20x^2 + 37x  -25}{(x-2)^3(x-1)} = \frac{A}{x - 1} + \frac{B}{(x -2)^3} + \frac{C}{(x-2)^2}+\frac{d}{x-2}.\]Enter the order quadruple $(A,B,C,d).$ -/
theorem algebra_20980 {A B C d : ℝ} (h : RatFunc.mk (4 * X ^ 3 - 20 * X ^ 2 + 37 * X - 25 : ℝ[X]) ((X - 2) ^ 3 * (X - 1)) = .mk (.C A) (X - 1) + .mk (.C B) ((X - 2) ^ 3) + .mk (.C C) ((X - 2) ^ 2) + .mk (.C d) (X - 2)) : A = 4 ∧ B = 1 ∧ C = 4 ∧ d = 0 := by
  apply congrArg (fun x ↦ x.toFractionRing) at h
  simp only [RatFunc.mk, ← RatFunc.ofFractionRing_add] at h
  -- Multiplying both sides by the denominator $(X - 2)^3(X - 1)$
  have h1 : (algebraMap ℝ[X] (FractionRing ℝ[X]) (4 * X ^ 3 - 20 * X ^ 2 + 37 * X - 25) / algebraMap ℝ[X] (FractionRing ℝ[X]) ((X - 2) ^ 3 * (X - 1))) * (algebraMap ℝ[X] (FractionRing ℝ[X]) ((X - 2) ^ 3 * (X - 1))) = (algebraMap ℝ[X] (FractionRing ℝ[X]) (.C A) / algebraMap ℝ[X] (FractionRing ℝ[X]) (X - 1) + algebraMap ℝ[X] (FractionRing ℝ[X]) (.C B) / algebraMap ℝ[X] (FractionRing ℝ[X]) ((X - 2) ^ 3) + algebraMap ℝ[X] (FractionRing ℝ[X]) (.C C) / algebraMap ℝ[X] (FractionRing ℝ[X]) ((X - 2) ^ 2) + algebraMap ℝ[X] (FractionRing ℝ[X]) (.C d) / algebraMap ℝ[X] (FractionRing ℝ[X]) (X - 2)) * (algebraMap ℝ[X] (FractionRing ℝ[X]) ((X - 2) ^ 3 * (X - 1))) := by
    rw [h]
  -- Simplifying left side
  have h2 : (algebraMap ℝ[X] (FractionRing ℝ[X]) (4 * X ^ 3 - 20 * X ^ 2 + 37 * X - 25) / algebraMap ℝ[X] (FractionRing ℝ[X]) ((X - 2) ^ 3 * (X - 1))) * (algebraMap ℝ[X] (FractionRing ℝ[X]) ((X - 2) ^ 3 * (X - 1))) = algebraMap ℝ[X] (FractionRing ℝ[X]) (4 * X ^ 3 - 20 * X ^ 2 + 37 * X - 25) := by
    calc
      _ = (algebraMap ℝ[X] (FractionRing ℝ[X]) (4 * X ^ 3 - 20 * X ^ 2 + 37 * X - 25)) * ((algebraMap ℝ[X] (FractionRing ℝ[X]) ((X - 2) ^ 3 * (X - 1))) / (algebraMap ℝ[X] (FractionRing ℝ[X]) ((X - 2) ^ 3 * (X - 1)))) := by ring_nf
      _ = algebraMap ℝ[X] (FractionRing ℝ[X]) (4 * X ^ 3 - 20 * X ^ 2 + 37 * X - 25) := by
        rw [div_self, mul_one]
        -- Proving $(X - 2)^3(X - 1) \neq 0$
        refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ?_
        refine Monic.mem_nonZeroDivisors ?_
        refine Monic.mul ?_ ?_
        refine Monic.pow ?_ 3
        have mid : (2 : ℝ[X]) = .C 2 := by exact rfl
        rw [mid]
        exact monic_X_sub_C 2
        have mid : (1 : ℝ[X]) = .C 1 := by exact rfl
        rw [mid]
        exact monic_X_sub_C 1
  rw [h2] at h1
  -- Simplifying right side
  simp only [add_mul] at h1
  -- $A / (X - 1) * (X - 2)^3(X - 1) = A(X - 2)^3$
  have h3 : (algebraMap ℝ[X] (FractionRing ℝ[X])) (.C A) / (algebraMap ℝ[X] (FractionRing ℝ[X])) (X - 1) * (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 3 * (X - 1)) = algebraMap ℝ[X] (FractionRing ℝ[X]) (.C A * (X - 2) ^ 3) := by
    calc
      _ = (algebraMap ℝ[X] (FractionRing ℝ[X])) (.C A) * (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 3) * ((algebraMap ℝ[X] (FractionRing ℝ[X])) (X - 1) / (algebraMap ℝ[X] (FractionRing ℝ[X])) (X - 1)) := by
        rw [map_mul]
        ring
      _ = _ := by
        rw [div_self, mul_one, map_mul]
        -- Proving $X - 1 \neq 0$
        refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ?_
        refine Monic.mem_nonZeroDivisors ?_
        exact monic_X_sub_C 1
  -- $B / (X - 2)^3 * (X - 2)^3(X - 1) = B(X - 1)$
  have h4 : (algebraMap ℝ[X] (FractionRing ℝ[X])) (.C B) / (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 3) * (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 3 * (X - 1)) = algebraMap ℝ[X] (FractionRing ℝ[X]) (.C B * (X - 1)) := by
    calc
      _ = (algebraMap ℝ[X] (FractionRing ℝ[X])) (.C B) * (algebraMap ℝ[X] (FractionRing ℝ[X])) (X - 1) * ((algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 3) / (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 3)) := by
        rw [map_mul]
        ring
      _ = _ := by
        rw [div_self, mul_one, map_mul]
        -- Proving $X - 2 \neq 0$
        refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ?_
        refine Monic.mem_nonZeroDivisors ?_
        refine Monic.pow ?_ 3
        have mid : (2 : ℝ[X]) = .C 2 := by exact rfl
        rw [mid]
        exact monic_X_sub_C 2
  -- $C / (X - 2)^2 * (X - 2)^3(X - 1) = C(X - 2)$
  have h5 : (algebraMap ℝ[X] (FractionRing ℝ[X])) (.C C) / (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 2) * (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 3 * (X - 1)) = algebraMap ℝ[X] (FractionRing ℝ[X]) (.C C * (X - 1) * (X - 2)) := by
    calc
      _ = (algebraMap ℝ[X] (FractionRing ℝ[X])) (.C C) * (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 1) * (X - 2)) * ((algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 2) / (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 2)) := by
        simp only [map_mul, map_pow]
        ring
      _ = _ := by
        rw [div_self, mul_one]
        simp only [map_mul, map_pow]
        ring
        -- Proving $(X - 2)^2 \neq 0$
        refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ?_
        refine Monic.mem_nonZeroDivisors ?_
        refine Monic.pow ?_ 2
        have mid : (2 : ℝ[X]) = .C 2 := by exact rfl
        rw [mid]
        exact monic_X_sub_C 2
  -- $d / (X - 2) * (X - 2)^3(X - 1) = d(X - 2)^2$
  have h6 : (algebraMap ℝ[X] (FractionRing ℝ[X])) (.C d) / (algebraMap ℝ[X] (FractionRing ℝ[X])) (X - 2) * (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 3 * (X - 1)) = algebraMap ℝ[X] (FractionRing ℝ[X]) (.C d * (X - 1) * (X - 2) ^ 2) := by
    calc
      _ = (algebraMap ℝ[X] (FractionRing ℝ[X])) (.C d) * (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 1) * (X - 2) ^ 2) * ((algebraMap ℝ[X] (FractionRing ℝ[X])) (X - 2) / (algebraMap ℝ[X] (FractionRing ℝ[X])) (X - 2)) := by
        simp only [map_mul, map_pow]
        ring
      _ = _ := by
        rw [div_self, mul_one]
        simp only [map_mul, map_pow]
        ring
        -- Proving $X - 2 \neq 0$
        refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ?_
        refine Monic.mem_nonZeroDivisors ?_
        exact monic_X_sub_C 2
  rw [h3, h4, h5, h6] at h1
  simp only [← map_add] at h1
  -- We have $4X^3 - 20X^2 + 37X - 25 = A(X - 2)^3 + B(X - 2) + C(X - 1)(X - 2) + d(X - 1)(X - 2)^2$
  apply NoZeroSMulDivisors.algebraMap_injective ℝ[X] (FractionRing ℝ[X]) at h1
  -- Setting $x=2$ gives $4(8)-20(4)+74-25=B$. Evaluating the expression on the left gives us $B=1$.
  have hB : (aeval (2 : ℝ)) (4 * X ^ 3 - 20 * X ^ 2 + 37 * X - 25 : ℝ[X]) = (aeval 2) (.C A * (X - 2) ^ 3 + .C B * (X - 1) + .C C * (X - 1) * (X - 2) + .C d * (X - 1) * (X - 2) ^ 2) := by
    rw [h1]
  simp at hB
  norm_num at hB
  symm at hB
  -- Setting $x=1$ gives $4-20+37-25=A$. Evaluating the expression on the left gives us $A=4$.
  have hA : (aeval (1 : ℝ)) (4 * X ^ 3 - 20 * X ^ 2 + 37 * X - 25 : ℝ[X]) = (aeval 1) (.C A * (X - 2) ^ 3 + .C 1 * (X - 1) + .C C * (X - 1) * (X - 2) + .C d * (X - 1) * (X - 2) ^ 2) := by
    rw [h1, hB]
  simp at hA
  norm_num at hA
  symm at hA
  -- Setting $x=0$ gives $2C-d = 8$.
  have hCD1 : (aeval (0 : ℝ)) (4 * X ^ 3 - 20 * X ^ 2 + 37 * X - 25 : ℝ[X]) = (aeval 0) (.C 4 * (X - 2) ^ 3 + .C 1 * (X - 1) + .C C * (X - 1) * (X - 2) + .C d * (X - 1) * (X - 2) ^ 2) := by
    rw [h1, hB, hA]
  simp at hCD1
  norm_num at hCD1
  symm at hCD1
  rw [add_assoc, add_comm (-33), ← sub_eq_add_neg] at hCD1
  apply eq_add_of_sub_eq at hCD1
  apply congrArg (fun x ↦ x / 2) at hCD1
  ring_nf at hCD1
  -- When $x=-1$, we get $$4(-1)^3-20(-1)^2+37(-1)-25=4(-3)^3+(-2)+C(-2)(-3)+d(-2)(-3)^2$$which simplifies to $$C-3D=4.
  have hCD2 : (aeval (-1 : ℝ)) (4 * X ^ 3 - 20 * X ^ 2 + 37 * X - 25 : ℝ[X]) = (aeval (-1)) (.C 4 * (X - 2) ^ 3 + .C 1 * (X - 1) + .C C * (X - 1) * (X - 2) + .C d * (X - 1) * (X - 2) ^ 2) := by
    rw [h1, hB, hA]
  simp at hCD2
  norm_num at hCD2
  symm at hCD2
  rw [add_assoc, add_comm (-110), ← sub_eq_add_neg] at hCD2
  apply eq_add_of_sub_eq at hCD2
  apply congrArg (fun x ↦ x / 6) at hCD2
  ring_nf at hCD2
  -- Solving the system of equations $2C-d=8$ and $C-3D=4$ gives $C=4$ and $d=0$.
  apply eq_add_of_sub_eq at hCD1
  rw [hCD1] at hCD2
  ring_nf at hCD2
  have hD : d = 0 := by
    apply congrArg (fun x ↦ -x) at hCD2
    apply congrArg (fun x ↦ x + 4) at hCD2
    ring_nf at hCD2
    exact hCD2
  have hC : C = 4 := by
    rw [hD] at hCD1
    ring_nf at hCD1
    exact hCD1
  exact ⟨hA, hB, hC, hD⟩
