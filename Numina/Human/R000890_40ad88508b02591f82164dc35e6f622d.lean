import Mathlib
open Polynomial
/-The roots of $x^4 - Kx^3 + Kx^2 + Lx + M = 0$ are $a,$ $b,$ $c,$ and $d.$   If $K,$ $L,$ and $M$ are real numbers, compute the minimum value of the sum $a^2 + b^2 + c^2 + d^2.$-/
theorem algebra_18912 (K L M : ℝ) (a b c d : ℝ)(hf : (f : Polynomial ℝ) = (C (1 : ℝ)) * X ^ 4 + (C (-K)) * X ^ 3 + (C K) * X ^ 2 + (C L) * X  + (C M))(h : f.roots =
    {a , b , c , d}) : K = 1 → IsLeast {e |  e = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2} (-1 : ℝ) := by
    --Confirm polynomial degree
    have hd : Polynomial.natDegree f = 4 := by
      rw [hf]
      compute_degree!
    --Confirm polynomial coeff
    have hc4 : f.coeff 4 = 1 := by simp [hf]
    have hc3 : f.coeff 3 = (-K) := by simp [hf]
    have hc2 : f.coeff 2 =  K := by simp [hf]
    --By Vieta's formulas, $a + b + c + d = K$
    have hp : Polynomial.coeff f 3 = Polynomial.leadingCoeff f * (-1) ^ (Polynomial.natDegree f - 3) * Multiset.esymm (Polynomial.roots f) (Polynomial.natDegree f - 3) := by
      apply Polynomial.coeff_eq_esymm_roots_of_card
      rw[h]; rw [hd]; simp
      rw [hd]; simp
    rw [hd,h] at hp
    simp [Multiset.esymm] at hp; rw [Multiset.powersetCard_one,Polynomial.leadingCoeff,hd,hc3,hc4] at hp; simp at hp
    have e:= congrArg (fun (t) => (t) * -1) hp; simp at e;rw [show d + c + b + a = a + b + c + d by ring_nf] at e
    --By Vieta's formulas, $ab + ac + ad + bc + bd + cd = K.$
    have hp2 : Polynomial.coeff f 2 = Polynomial.leadingCoeff f * (-1) ^ (Polynomial.natDegree f - 2) * Multiset.esymm (Polynomial.roots f) (Polynomial.natDegree f - 2) := by
      apply Polynomial.coeff_eq_esymm_roots_of_card
      rw[h]; rw [hd]; simp
      rw [hd]; linarith
    rw [hd] at hp2;rw [h]  at hp2; simp at hp2; rw [Polynomial.leadingCoeff] at hp2; rw [hd] at hp2; rw [hc2] at hp2; rw [hc4] at hp2
    simp [Multiset.esymm] at hp2;  rw [Multiset.powersetCard_one] at hp2; simp at hp2; ring_nf at hp2
    --Squaring the equation $a + b + c + d = K,$ we get\[a^2 + b^2 + c^2 + d^2 + 2(ab + ac + ad + bc + bd + cd) = K^2.\]Hence,\[a^2 + b^2 + c^2 + d^2 = K^2 - 2K = (K - 1)^2 - 1.\]
    have hk : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (K - 1 ) ^ 2 - 1 := by
      have heq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = (a + b + c + d) ^2 - 2 *(c * d + c * b + c * a + d * b + d * a + b * a) := by  ring_nf
      rw [heq]; rw [← e] ; rw [← hp2]
      ring_nf
    --This expression is minimized at $K = 1,$ with a minimum value of $\boxed{-1}.$
    intro hk2
    simp_rw [hk,hk2]
    rw [IsLeast]; norm_num
