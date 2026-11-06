import Mathlib

/- 2. If $a_{1}, a_{2}, a_{3}, \ldots, a_{n}$ are positive real numbers such that $a_{1} a_{2} a_{3} \ldots a_{n}=1$, then
$$
\left(1+a_{1}\right)\left(1+a_{2}\right)\left(1+a_{3}\right) \ldots\left(1+a_{n}\right) \geq 2^{n}
$$
Prove! -/
theorem inequalities_222228 (n : ℕ) (a : Fin n → ℝ)
    (h₀ : ∀ i, 0 < a i) (h₁ : ∏ i, a i = 1) :
    ∏ i, (1 + a i) ≥ 2 ^ n := by
  -- Show that for any 0 ≤ x we have 2 * √x ≤ 1 + x.
  have ineq {x : ℝ} (hx : 0 ≤ x) : 2 * √x ≤ 1 + x := calc
    -- 2 * √x = 2 * 1 * √x
    --        ≤ 1^2 + √x^2 (since 2 * a * b ≤ a^2 + b^2 for any a and b)
    --        = 1 + x (since 0 ≤ x).
    2 * √x = 2 * 1 * √x := by ring
    _ ≤ 1 ^ 2 + √x ^ 2 := two_mul_le_add_pow_two 1 √x
    _ = 1 + x := by simp [Real.sq_sqrt hx]
  rw [ge_iff_le]
  calc
    -- We have
    -- 2 ^ n = ∏ i, 2 * a(i)^(1 / 2) (since (∏ i, a(i))^(1 / 2) = 1 ^ (1/2) = 1).
    --       = ∏ i, 2 * √a(i)
    --       ≤ ∏ i, (1 + a(i)) (from ineq).
    2 ^ n = ∏ i, (2 * (a i) ^ (1 / 2 : ℝ)) := by
      rw [← Finset.pow_card_mul_prod, Real.finset_prod_rpow _ _ (fun i _ => le_of_lt <| h₀ i)]
      simp [h₁]
    _  ≤ ∏ i, (1 + a i) := by
      apply Finset.prod_le_prod
      · intro i hi
        apply mul_nonneg zero_le_two
        apply Real.rpow_nonneg
        exact le_of_lt (h₀ i)
      · intro i hi
        rw [← Real.sqrt_eq_rpow]
        apply ineq
        exact le_of_lt (h₀ i)