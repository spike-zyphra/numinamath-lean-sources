import Mathlib

/- Compute

$$
\frac{2+3+\cdots+100}{1}+\frac{3+4+\cdots+100}{1+2}+\cdots+\frac{100}{1+2+\cdots+99} .
$$-/
theorem algebra_610798 :
    ∑ i in Finset.Icc 1 (99 : ℕ), (∑ j in Finset.Icc (i + 1) 100, j : ℚ) / (∑ j in Finset.Icc 1 i, j : ℚ) = 9900 := by
  -- Add 99 to both sides.
  suffices ∑ i in Finset.Icc 1 (99 : ℕ), (∑ j in Finset.Icc (i + 1) 100, j : ℚ) / (∑ j in Finset.Icc 1 i, j : ℚ) + ∑ i in Finset.Icc 1 99, 1 = 9900 + ∑ i in Finset.Icc 1 99, 1 by
    simpa
  rw [<-Finset.sum_add_distrib]
  norm_num
  -- Prove the lemma that ∑ i in Finset.Icc 1 n = n * (n + 1) / 2.
  have h₀ (n : ℕ) : ∑ i in Finset.Icc 1 n, i = n * (n + 1) / 2 := by
    induction n with
    | zero =>
      simp
    | succ n hn =>
      rw [Finset.sum_Icc_succ_top (by norm_num), hn, add_assoc, mul_add _ _ (1 + 1)]
      norm_num
      rw [Nat.add_mul_div_right _ _ (by norm_num)]
      ac_rfl
  -- Prove the equality step by step.
  calc
    ∑ i in Finset.Icc 1 (99 : ℕ), ((∑ j in Finset.Icc (i + 1) 100, j : ℚ) / (∑ j in Finset.Icc 1 i, j : ℚ) + 1)
    _ = ∑ i in Finset.Icc 1 (99 : ℕ), (∑ j in Finset.Icc 1 (100 : ℕ), j : ℚ) / (∑ j in Finset.Icc 1 i, j : ℚ) := by
      -- We add one to each fraction.
      rw [Finset.sum_congr rfl]
      intro i hi
      simp at hi
      rw [div_add_one, add_comm, show Finset.Icc 1 i = Finset.Ico 1 (i + 1) by tauto, show Finset.Icc (i + 1) 100 = Finset.Ico (i + 1) 101 by tauto, Finset.sum_Ico_consecutive]
      rfl
      omega
      omega
      -- Justify that the denominator is not zero.
      specialize h₀ i
      qify at h₀
      rw [h₀]
      by_contra!
      norm_cast at this
      have h₁ : i * (i + 1) ≥ 2 := by
        nlinarith
      omega
    _ = ∑ i in Finset.Icc 1 (99 : ℕ), ((100 * 101 / 2 : ℕ) : ℚ) / ((i * (i + 1) / 2 : ℕ) : ℚ) := by
      rw [Finset.sum_congr rfl]
      intro i hi
      simp at hi
      have h₀' := h₀ i
      have h₀'' := h₀ 100
      qify at h₀' h₀''
      norm_cast at h₀' h₀''
      rw [h₀', h₀'']
    _ = 10100 * ∑ i in Finset.Icc 1 (99 : ℕ), (-1 / ((i + 1 : ℕ) : ℚ) - -1 / (i : ℚ)) := by
      rw [Finset.mul_sum, Finset.sum_congr rfl]
      intro i hi
      simp at hi
      have h₁ : i * (i + 1) ≥ 2 := by
        nlinarith
      field_simp [show i * (i + 1) / 2 ≠ 0 by omega, show i ≠ 0 by omega]
      norm_cast
      rw [<-Nat.mul_div_assoc, mul_comm 10100, Nat.mul_div_assoc (i * (i + 1))]
      norm_num
      ac_rfl
      norm_num
      -- Verify that 2 ∣ i(i + 1).
      have h₂ : i % 2 = 0 ∨ i % 2 = 1 := by
        omega
      rw [Nat.dvd_iff_mod_eq_zero]
      rcases h₂ with (h₂ | h₂)
      <;> simp [mul_add, Nat.add_mod, Nat.mul_mod, h₂]
    _ = 9999 := by
      -- The sum is telescoping.
      rw [show Finset.Icc 1 99 = (Finset.range 100).erase 0 by rfl, Finset.sum_erase_eq_sub, Finset.sum_range_sub (λ x => -1 / (x : ℚ))]
      norm_num
      simp
