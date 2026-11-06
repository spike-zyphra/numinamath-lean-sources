import Mathlib

/- 1. Prove that for different natural numbers $a_{1}, a_{2}, \ldots, a_{n}$ the following holds


$$

\left(a_{1}+a_{2}+\ldots+a_{n}\right)^{2} \leq a_{1}^{3}+a_{2}^{3}+\ldots+a_{n}^{3}

$$
 -/
theorem inequalities_245546 (n : ℕ) (a : Fin n → ℕ) (ha : a.Injective) :
    (∑ i, a i) ^ 2 ≤ ∑ i, (a i) ^ 3
  := by
    -- wlog, a is monotone
    wlog hm : Monotone a
    · let g := Tuple.sort a
      convert this n (a <| g ·) (ha.comp g.injective) (Tuple.monotone_sort a) using 1
      · rw [Equiv.sum_comp]
      · rw [Equiv.sum_comp g (fun x => a x ^ 3)]

    -- a is monotone and injective, so it's strictly monotone
    have strictmono := hm.strictMono_of_injective ha

    -- we will prove the inequality by induction on n
    induction' n with k ih
    -- when n = 0, both sides are zero
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, le_refl]
    -- Then we have a = a_1, .., a_(k+1). let a' be a_1, .., a_k
    · let a' : Fin k → ℕ := fun i => a i.castSucc
      have a_inj' : a'.Injective := ha.comp <| Fin.castSucc_injective k
      have a_mono' : Monotone a' := hm.comp (@Fin.strictMono_castSucc k).monotone
      have a_strictmono' : StrictMono a' := a_mono'.strictMono_of_injective a_inj'
      have ind := ih a' a_inj' a_mono' a_strictmono'

      -- we have that 2 * (∑ i : Fin k, a_i) ≤ a_(k+1) ^ 2 - a_(k+1)
      have sum_bound : 2 * (∑ i : Fin k, a' i) ≤ a (Fin.last k) ^ 2 - a (Fin.last k) := by
        calc 2 * (∑ i : Fin k, a' i)
        -- The sum is less than the sum of 1..a_(k+1)
        _ ≤ 2 * (∑ i ∈ Finset.range (a (Fin.last k)), i) := by
          gcongr
          -- make it clear we are summing over an injective function
          convert_to ∑ i : Fin k, id ((⟨a', a_inj'⟩ : Fin k ↪ ℕ) i) ≤ ∑ i ∈ Finset.range (a (Fin.last k)), i
          rw [←Finset.sum_map]
          -- LHS is sum of a subset of RHS, so it's smaller
          apply Finset.sum_le_sum_of_subset
          intro aa bb
          simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and, a'] at bb
          obtain ⟨i, ih⟩ := bb
          rw [Finset.mem_range, ←ih]
          -- use that a is monotone
          apply strictmono
          exact Fin.castSucc_lt_last i
        _ = a (Fin.last k) ^ 2 - a (Fin.last k) := by
          -- Gauss' summation formula
          rw [mul_comm, Finset.sum_range_id_mul_two, Nat.mul_sub, pow_two, mul_one]

      -- So we have a lower bound of a_(k+1) ^ 3
      have le_last_cube : 2 * (∑ i : Fin k, a' i) * a (Fin.last k) + a (Fin.last k) ^ 2 ≤ a (Fin.last k) ^ 3
        := by
          -- multiple both sides of the bound by a_(k+1)
          replace sum_bound := Nat.mul_le_mul_right (a (Fin.last k)) sum_bound
          -- simplify
          rw [Nat.sub_mul] at sum_bound
          -- we have the bound
          convert Nat.add_le_of_le_sub ?_ sum_bound using 1
          · simp only [add_right_inj]
            exact Nat.pow_two (a (Fin.last k))
          apply Nat.mul_le_mul_right
          refine Nat.le_self_pow ?_ (a (Fin.last k))
          omega
      -- split up sums on both sides to apply our bounds
      rw [Fin.sum_univ_castSucc, add_sq, Fin.sum_univ_castSucc]
      convert_to (∑ i : Fin k, a i.castSucc) ^ 2 + ((2 * ∑ i : Fin k, a i.castSucc) * a (Fin.last k) + a (Fin.last k) ^ 2)
        ≤ ∑ i : Fin k, a i.castSucc ^ 3 + a (Fin.last k) ^ 3
      · ring
      -- inequality of terms gives us inequality of sum
      exact Nat.add_le_add ind le_last_cube