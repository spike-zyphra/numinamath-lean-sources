import Mathlib

open Finset Real

/- 22. Prove the inequality:
$$
\left(a_{1}+a_{2}+\ldots+a_{n}\right)\left(\frac{1}{a_{1}}+\frac{1}{a_{2}}+\ldots+\frac{1}{a_{n}}\right) \geqslant n^{2}
$$
$\left(a_{1}, a_{2}, \ldots, a_{n}\right.$ - positive numbers). (U. 124, P. 187.) -/

theorem inequalities_257990 {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ) (ha : ∀ i ∈ range n, 0 < a i) :
        (∑ i ∈ range n, a i) * (∑ i ∈ range n, 1 / a i) ≥ n ^ 2 := by 
    --consider the Cauchy-Schwarz inequality with (√a i) and (1/√ a i).
    have := @real_inner_mul_inner_self_le (EuclideanSpace ℝ (Fin n)) _ _ (fun i => sqrt (a i)) (fun i => 1 / (sqrt (a i)))
    simp at this
    --after some routinal algebraic checks it yields the claim immediatly
    have eq_sum1 : ∀ i ∈ range n, √(a i) * (√(a i))⁻¹ = 1 := by 
        intro i hi
        field_simp
        exact div_self ((sqrt_ne_zero (le_of_lt (ha i hi))).mpr (by specialize ha i hi; linarith))
    have eq_sum2 : ∀ i ∈ range n, √(a i) * (√(a i)) = a i := by 
        intro i hi
        rw[← sqrt_mul (le_of_lt (ha i hi))]
        exact sqrt_mul_self (le_of_lt (ha i hi))
    have eq_sum3 : ∀ i ∈ range n, (√(a i))⁻¹ * (√(a i))⁻¹ = (a i)⁻¹ := by 
        intro i hi
        field_simp
        rw[← sqrt_mul (le_of_lt (ha i hi)), sqrt_mul_self (le_of_lt (ha i hi))]
    rw[← sq, ← Finset.sum_range (fun i => √(a i) * (√(a i))⁻¹), (Finset.sum_eq_sum_iff_of_le (by intro i hi; exact le_of_eq (eq_sum1 i hi))).2 eq_sum1] at this
    rw[← Finset.sum_range (fun i => √(a i) * (√(a i))), (Finset.sum_eq_sum_iff_of_le (by intro i hi; exact le_of_eq (eq_sum2 i hi))).2 eq_sum2] at this
    rw[← Finset.sum_range (fun i => (√(a i))⁻¹ * (√(a i))⁻¹), (Finset.sum_eq_sum_iff_of_le (by intro i hi; exact le_of_eq (eq_sum3 i hi))).2 eq_sum3] at this
    simp at this
    field_simp at this
    exact this