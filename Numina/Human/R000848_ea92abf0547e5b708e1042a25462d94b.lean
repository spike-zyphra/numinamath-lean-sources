import Mathlib
/-If the roots of the quadratic equation $\frac12x^2+99x+c=0$ are $x=-99+\sqrt{8001}$ and $x=-99-\sqrt{8001}$, then what is the value of $c$?-/
open Polynomial
theorem algebra_18577 {c : ℝ}(hf: (f : Polynomial ℝ) =(C (1 / 2)) * X^2 + (C 99) * X + (C c)) (h : f.roots =
    { -99 + Real.sqrt 8001, -99 - Real.sqrt 8001}):
    c = 900 := by
    --By the quadratic formula, the roots of the equation are $$x=\frac{-(99)\pm\sqrt{(99)^2-4(\frac12)c}}{2(\frac12)},$$which simplifies to $$x=-99\pm\sqrt{9801-2c}.$$This looks like our target, except that we have to get the $9801-2c$ under the radical to equal $8001$. So, we solve the equation $9801-2c=8001$, which yields $c=\boxed{900}$.
    have coeff_c : f.coeff 0 = c := by simp [hf]
    have hd : f.degree = 2 := by
      rw [hf]
      compute_degree!
    have  hd2 :  Polynomial.natDegree f = 2 := by 
      rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos]
      exact hd
      simp
    have hp : Polynomial.coeff f 0 = Polynomial.leadingCoeff f * (-1) ^ (Polynomial.natDegree f - 0) * Multiset.esymm (Polynomial.roots f) (Polynomial.natDegree f - 0) := by
      apply Polynomial.coeff_eq_esymm_roots_of_card
      rw[h]; rw [hd2]
      simp
      rw [hd2]
      simp
    rw [hd2] at hp
    rw [h]  at hp
    simp at hp
    rw [Polynomial.leadingCoeff] at hp; rw [hd2] at hp
    have hf2 : f.coeff 2 = 1 / (2 : ℝ) := by 
      rw [hf]
      simp
    rw [hf2] at hp
    have heq : 1 / 2 * ((-99 + √8001) ::ₘ {-99 - √8001}).esymm 2 = 900 := by
      have heq2 :   ((-99 + √8001) ::ₘ {-99 - √8001}).esymm 2   =  (-99 + Real.sqrt 8001) * (-99 - Real.sqrt 8001) := by
        simp [Multiset.esymm]
        rw [Multiset.powersetCard_one]
        simp
      rw [heq2]
      ring_nf
      have sqrt8001: √8001 ^ 2 = 8001 := by
        rw [Real.sq_sqrt]
        linarith
      rw [sqrt8001]
      ring_nf
    rw [heq] at hp ; rw [coeff_c] at hp
    exact hp