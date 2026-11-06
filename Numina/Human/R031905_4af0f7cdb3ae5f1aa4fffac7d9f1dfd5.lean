import Mathlib

open Real
open scoped BigOperators

/- 308*. Prove that $n a_{1} a_{2} \ldots a_{n} \leqslant a_{1}^{n}+a_{2}^{n}+\ldots+a_{n}^{n}$, where $n-$ is a natural number, $a_{i}$-positive numbers.[^8]

84 -/
theorem inequalities_277168 {n : ℕ} (a : Fin n → ℝ)
  (h₀ : ∀ i, 0 < a i) :
  n * ∏ i, a i ≤ ∑ i, (a i)^n := by
  -- we need to handle n=0 separately
  match n with
  | 0 => simp
  | m+1 =>
    -- use AM-GM to go ∏ a_i = nth √ (∏ a_i^n) ≤ 1/n * ∑ a_i^n
    have q:= Real.geom_mean_le_arith_mean (by exact Finset.univ) (fun i=> 1) (fun i=> (a i)^(m+1)) (by simp) (by simp; exact Nat.cast_add_one_pos _) (by simp; intro i; apply pow_nonneg; linarith [h₀ i])
    simp at q
    -- we simplify the lhs
    conv_lhs at q =>
      calc (∏ x : Fin (m + 1), a x ^ (m + 1)) ^ ((m:ℝ) + 1)⁻¹
      _ = (∏ x : Fin (m + 1), (a x ^ (m + 1)) ^ (((m:ℝ) + 1)⁻¹) ) := by rw [← finset_prod_rpow]; intro i hi; apply pow_nonneg; linarith [h₀ i]
      _ = (∏ x : Fin (m + 1), (a x ^ ((m:ℝ)+1)) ^ (((m:ℝ) + 1)⁻¹) ) := by norm_cast
      _ = (∏ x : Fin (m + 1), a x) := by conv => lhs; rhs; intro x; rw [← rpow_mul (by linarith [h₀ x]), mul_inv_cancel₀ (by exact Nat.cast_add_one_ne_zero m), rpow_one];

    -- we multiply both sides by (m+1)
    have q2:= (mul_le_mul_left (a:=(m+1:ℝ)) (b:=∏ i : Fin (m + 1), a i) (c:=(∑ i : Fin (m + 1), a i ^ (m + 1))/ (m + 1:ℝ)) (by exact Nat.cast_add_one_pos m)).mpr q
    -- and simplify
    conv_rhs at q2 => rw [← mul_div_assoc, mul_comm, mul_div_assoc, div_self (by exact Nat.cast_add_one_ne_zero m), mul_one]
    norm_cast at q2