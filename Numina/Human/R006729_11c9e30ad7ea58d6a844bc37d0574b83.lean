import Mathlib

open Nat Finset

/-Let $p$ be a prime number and $k$ be an integer such that $1 \le k < p$.
Suppose that $(k-1)! \equiv (-1)^{k-1} \pmod p$.
Show that $(p-k)!+1$ is divisible by $p$.-/
theorem p_divides_p_minus_k_factorial_plus_one
    (p : ℕ) [p_prime : Fact p.Prime]
    (k : ℕ) (hk_ge_one : 1 ≤ k) (hk_lt_p : k < p)
    (h_hyp : (↑((k-1)!) : ℤ) ≡ (-1)^(k-1) [ZMOD ↑p]) :
    p ∣ (p-k)! + 1 := by
  -- The goal `p ∣ n + 1` is equivalent to `n = -1` in the finite field `ZMod p`.
  -- We use the corrected lemma name here.
  -- rw [ZMod.nat_dvd_add_one_iff_cast_eq_neg_one]

  -- First, we prove that the product part of the factorial expansion equals 1 in `ZMod p`.
  -- This is a key helper result for the main proof.
  have prod_val_is_one : (∏ i ∈ Ico (p - k + 1) p, (i : ZMod p)) = 1 :=
    calc
      -- Start with the product
      (∏ i ∈ Ico (p - k + 1) p, (i : ZMod p))
      -- Step 1: Reverse the order of the product using `prod_Ico_reflect`.
      _ = (∏ i ∈ Ico 1 k, (↑(p - i) : ZMod p)) := by
          -- Use bijection between the two ranges
          rw [← Finset.prod_bij']
          · -- forward map: i ↦ p - i
            exact fun i _ => p - i
          · -- reverse map: j ↦ p - j
            exact fun j _ => p - j
          · -- i is in first range implies p-i is in second range
            intro i hi
            simp at hi ⊢
            omega
          · -- j is in second range implies p-j is in first range
            intro j hj
            simp at hj ⊢
            omega
          · -- functions are inverses
            intro i hi
            apply Nat.sub_sub_self
            have : i ≤ k := le_of_lt (mem_Ico.mp hi).2
            omega
          · -- functions are inverses
            intro j hj
            apply Nat.sub_sub_self
            have : j ≤ p := le_of_lt (mem_Ico.mp hj).2
            omega
          · -- the values are equal
            intro i hi
            simp
      -- Step 2: In `ZMod p`, `p - i` is the same as `-i`.
      _ = (∏ i ∈ Ico 1 k, (-↑i : ZMod p)) := by
          apply prod_congr rfl
          intro i hi
          rw [Nat.cast_sub (le_of_lt (lt_trans (mem_Ico.mp hi).2 hk_lt_p))]
          have: (p : ZMod p) = 0 := by exact ZMod.natCast_self p
          rw [this, zero_sub]
      -- Step 3: Factor out the `-1` from each term in the product.
      _ = (-1)^(k - 1) * (∏ i ∈ Ico 1 k, (↑i : ZMod p)) := by
          rw [show ∏ i ∈ Ico 1 k, -↑i = ∏ i ∈ Ico 1 k, (-1 : ZMod p) * ↑i from
                prod_congr rfl (fun _ _ => by simp [neg_mul])]
          rw [prod_mul_distrib, prod_const, card_Ico]
      -- Step 4: The remaining product is the definition of `(k-1)!`.
      _ = (-1)^(k - 1) * ↑((k - 1)!) := by
          rw [← Nat.cast_prod]
          congr 1
          rw [show k = k - 1 + 1 from by omega, prod_Ico_id_eq_factorial (k - 1)]
          simp [Nat.sub_add_cancel hk_ge_one]
      -- Step 5: Use the given hypothesis to replace `(k-1)!`.
      _ = (-1)^(k - 1) * (-1)^(k - 1) := by
          have h_hyp_zmod : (↑(k - 1)! : ZMod p) = (-1)^(k - 1) := by
            -- Convert the Int congruence to a ZMod p equality
            rw [← ZMod.intCast_eq_intCast_iff,
                Int.cast_pow, Int.cast_neg, Int.cast_one] at h_hyp
            norm_num at h_hyp
            exact h_hyp
          rw [h_hyp_zmod]
      -- Step 6: Simplify the expression to 1.
      _ = 1 := by
          simp_rw [← mul_pow]
          norm_num

  -- Now we prove the main goal using another `calc` block.
  have h_2: (↑(p - k)! : ZMod p) = -1 := by
    calc
      -- Start with the term from the goal
      (↑(p - k)! : ZMod p)
      -- Step 1: Multiply by 1, which doesn't change the value.
      _ = (↑(p - k)!) * 1 := (mul_one _).symm
      -- Step 2: Substitute 1 with our proven product value.
      _ = (↑(p - k)!) * (∏ i ∈ Ico (p - k + 1) p, (i : ZMod p)) := by
          rw [prod_val_is_one]
      -- Step 3: Combine the terms into a single cast of a natural number product.
      _ = ↑((p - k)! * ∏ i ∈ Ico (p - k + 1) p, i) := by
          rw [Nat.cast_mul, Nat.cast_prod]
      -- Step 4: This product is the definition of `(p-1)!`.
      _ = ↑((p - 1)!) := by
          have h_expand_fact : (p - 1)! = (p - k)! * ∏ i ∈ Ico (p - k + 1) p, i := by
            calc
              _ = ∏ i ∈ Finset.Ico 1 (p - 1 + 1), i := by simp [Finset.prod_Ico_id_eq_factorial p]
              _ = ∏ i ∈ Finset.Ico 1 p, i := by congr; omega
              _ = (∏ i ∈ Finset.Ico 1 (p - k + 1), i) * (∏ i ∈ Finset.Ico (p - k + 1) p, i) := by
                rw [Finset.prod_Ico_consecutive] <;> omega
              _ = (p - k)! * (∏ i ∈ Finset.Ico (p - k + 1) p, i) := by simp [Finset.prod_Ico_id_eq_factorial (p - k)]
          rw [← h_expand_fact]
      -- Step 5: By Wilson's Theorem in `ZMod p`, `(p-1)! = -1`.
      _ = -1 := ZMod.wilsons_lemma p

  have h_3: p ∣ (p-k)! + 1 := by
    rw [← CharP.cast_eq_zero_iff (ZMod p), Nat.cast_add, Nat.cast_one]
    rw [add_eq_zero_iff_eq_neg]
    exact h_2

  exact h_3
