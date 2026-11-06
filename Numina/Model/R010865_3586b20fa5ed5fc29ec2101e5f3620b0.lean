import Mathlib

open Polynomial

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
  -- $C / (X - 2)^2 * (X - 2)^3(X - 1) = C(X - 1)(X - 2)$
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
  -- $d / (X - 2) * (X - 2)^3(X - 1) = d(X - 1)(X - 2)^2$
  have h6 : (algebraMap ℝ[X] (FractionRing ℝ[X])) (.C d) / (algebraMap ℝ[X] (FractionRing ℝ[X])) (X - 2) * (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 2) ^ 3 * (X - 1)) = algebraMap ℝ[X] (FractionRing ℝ[X]) (.C d * (X - 1) * (X - 2) ^ 2) := by
    calc
      _ = (algebraMap ℝ[X] (FractionRing ℝ[X])) (.C d) * (algebraMap ℝ[X] (FractionRing ℝ[X])) ((X - 1) * (X - 2) ^ 2) * ((algebraMap ℝ[X] (FractionRing ℝ[X])) (X - 2) / (algebraMap ℝ[X] (FractionRing ℝ[X])) (X - 2)) := by
        simp only [map_mul,  map_pow]
        ring
      _ = _ := by
        rw [div_self,  mul_one]
        simp only [map_mul,  map_pow]
        ring
        -- Proving $X - 2 \neq 0$
        refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ?_
        refine  Monic.mem_nonZeroDivisors  ?_
        exact monic_X_sub_C 2
  rw [h3, h4, h5, h6]  at h1
  simp only [← map_add] at h1
  -- We have $4X^3 - 20X^2 + 37X - 25 = A(X - 2)^3 + B(X - 1) + C(X - 1)(X - 2) + d(X - 1)(X - 2)^2$
  apply NoZeroSMulDivisors.algebraMap_injective ℝ[X] (FractionRing ℝ[X]) at h1
  -- Setting $x=1$ gives $4-20+37-25=A$. Evaluating the expression on the left gives us $A=4$.
  have eq1 := congr_arg (fun f => f.eval (1 : ℝ)) h1
  simp at  eq1
  have hA : A = 4 := by
    nlinarith
  -- Setting $x=2$ gives $1 = B$
  have eq2 := congr_arg (fun f => f.eval (2 : ℝ)) h1
  simp at  eq2
  have hB : B = 1 := by
    nlinarith
  -- Setting $x=0$ gives $2C-d = 8$
  have eq3 := congr_arg (fun f => f.eval (0 : ℝ)) h1
  simp at  eq3
  -- Setting $x=3$ gives $14 = 4 + 2 + 2C + 2d$ implies $2C + 2d = 8$
  have eq4 := congr_arg (fun f => f.eval (3 : ℝ)) h1
  simp at  eq4
  -- Solving the equations gives $C = 4$ and $d = 0$
  have hC : C = 4 := by
    nlinarith [hA, hB, eq3, eq4]
  have hd : d = 0 :=  by
    nlinarith [hA, hB, eq3, eq4]
  exact ⟨hA, hB, hC, hd⟩