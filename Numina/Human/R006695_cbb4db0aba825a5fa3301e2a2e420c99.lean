import Mathlib

open Nat

/--
Let `p` be a prime and `m` a positive integer.  Then the exponent of the highest power
of `p` dividing `(p^m - 1)!` is `(p^m - 1) / (p - 1) - m`.
-/
theorem v_p_factorial {p m : ℕ} (h_m: m > 0) [Fact (Nat.Prime p)]  :
  multiplicity p ((p ^ m - 1) !) = (p ^ m - 1) / (p - 1) - m := by

  -- Legendre's formula: multiplicity p (n!) = ∑_{k ≥ 1} ⌊n / p^k⌋
  have hp : Nat.Prime p := Fact.out
  have hp_gt_1 : 2 ≤ p := hp.one_lt
  have h_m_ge_1: m ≥ 1 := by linarith

  have h_p_m: p ^ m ≥ 2 := by
    calc
      _ ≥ p ^ 1 := by
        apply Nat.pow_le_pow_right
        all_goals omega
      _ ≥ 2 ^ 1 := by exact Nat.pow_le_pow_left hp_gt_1 1

  have h_log : log p (p^m - 1) < m := by
    -- `log p (p^m - 1) < log p (p^m) = m` because p > 1, and k < k + 1

    have h_log_p_m: log p (p^m) = m := log_pow hp_gt_1 m
    have h_eq : p ^ log p (p^m - 1 + 1) = p^m - 1 + 1:= by
      rw [show p^m - 1 + 1 = p^m by omega]
      rw [h_log_p_m]

    calc
      _ < log p (p^m - 1 + 1) := by 
        refine (lt_pow_iff_log_lt hp_gt_1 ?_).mp ?_
        exact Nat.sub_ne_zero_iff_lt.mpr h_p_m
        have t1: p ^ log p (p ^ m - 1 + 1)=(p ^ m - 1 + 1):=by exact h_eq
        rw[t1]
        linarith
      _ = log p (p^m) := by congr; omega
      _ = m := by rw [h_log_p_m]

  -- Apply Legendre's theorem (Nat.Prime.emultiplicity_factorial).
  have h_legendre :
    emultiplicity p ((p^m - 1).factorial) =
      ↑(∑ k ∈ Finset.Ico 1 m, (p^m - 1) / p ^ k) := by
    apply Nat.Prime.emultiplicity_factorial hp h_log

  -- assert that the emultiplicity is finite
  have h_finite : FiniteMultiplicity p (factorial (p^m - 1)) := by
    exact finiteMultiplicity_of_emultiplicity_eq_natCast h_legendre

  -- convert emultiplicity to multiplicity
  have h_legendre' :
    multiplicity p ((p^m - 1).factorial) = ∑ k ∈ Finset.Ico 1 m, (p^m - 1) / p ^ k := (FiniteMultiplicity.emultiplicity_eq_iff_multiplicity_eq h_finite).mp h_legendre


  -- evaluate each term in the sum
  have h_evaluated : ∀ k < m, (p ^ m - 1) / p ^ k = p ^ (m - k) - 1 := by
    intro k hk
    have : p ^ (m - k) - 1 ≥ 0 := by omega
    have h_div_mod : (p ^ k - 1) + p ^ k * (p ^ (m - k) - 1) = p ^ m - 1:= by
      calc
        _ = p ^ k * p ^ (m - k) - p ^ k + (p ^ k - 1) := by
          rw [mul_tsub]
          ring_nf
        _ = p ^ m - p ^ k + (p ^ k - 1) := by
          rw [<-pow_add]
          rw [show k + (m - k) = m by omega]
        _ = p ^ m - 1 := by
          refine Nat.sub_add_sub_cancel ?_ ?_
          . exact Nat.pow_le_pow_of_le hp_gt_1 (by linarith)
          . exact NeZero.one_le

    have h_p_k_pos : 0 < p ^ k := by positivity

    exact ((Nat.div_mod_unique h_p_k_pos).mpr ⟨h_div_mod, by omega⟩).1

  -- change the index of the sum; let's say `i = m - j` or `j = m - i`
  have h_sum_change_index:
      ∑ i ∈ Finset.Ico 1 m, p ^ (m - i) = ∑ j ∈ Finset.Ico 1 m, p ^ j := by
    apply Finset.sum_bij (fun i _hi => m - i)
    · -- Proof that (m - i) ∈ range m for i ∈ Ico 1 (m + 1)
      intro i hi
      simp
      have hi₁ : 1 ≤ i := (Finset.mem_Ico.mp hi).1
      have hi₂ : i < m := (Finset.mem_Ico.mp hi).2
      constructor
      . exact Nat.le_sub_of_add_le' hi₂
      . omega
    · -- Injectivity
      intro i₁ hi₁ i₂ hi₂ h_eq
      simp_all
      omega
    · -- Surjectivity
      intro j hj
      simp_all
      use m - j
      omega
    · -- Finally, show `p^(m - i) = p^(m - i)`
      intro i hi
      rfl

  -- Case 1: m = 1
  by_cases h_m_eq_1: m = 1
  . have : multiplicity p ((p ^ m - 1)!) = 0 := by
      simp only [h_legendre']
      rw [h_m_eq_1]
      norm_num
    rw [this, h_m_eq_1]
    norm_num
    rw [Nat.div_self (by omega)]

  -- Case 2: m > 1
  . calc multiplicity p ((p ^ m - 1)!)
      _ = ∑ k ∈ Finset.Ico 1 m, (p^m - 1) / p ^ k := by simp [h_legendre']

      -- evaluate each term in the sum
      _ = ∑ k ∈ Finset.Ico 1 m, (p ^ (m - k) - 1) := by
        have h : ∀ k, k ∈ Finset.Ico 1 m → (p^m - 1) / p^k = p^(m - k) - 1 := by
          intro k hk
          simp at hk
          exact h_evaluated k hk.2
        exact Finset.sum_congr rfl h

      -- split the sum into two parts
      _ = (∑ k in Finset.Ico 1 m, p ^ (m - k)) - (∑ k in Finset.Ico 1 m, 1) := by
        apply Finset.sum_tsub_distrib
        intro k hk
        simp at hk
        have: m - k ≥ 0 := by omega
        exact NeZero.one_le

      -- sum up the constant term
      _ = (∑ k in Finset.Ico 1 m, p ^ (m - k)) - (m - 1) := by
        simp [Finset.sum_sub_distrib]

      -- change the index of the sum; let's say `i = m - j` or `j = m - i`
      _ = (∑ j in Finset.Ico 1 m, p ^ j) - (m - 1) := by simp [h_sum_change_index]

      -- add the first term of the geometric series to apply `Nat.geomSum_eq`
      _ = (∑ j in Finset.range m, p ^ j) - 1 - (m - 1) := by
        have h_sum_two_parts : 1 + ∑ j in Finset.Ico 1 m, p ^ j = ∑ j in Finset.range m, p ^ j:= by
          rw [Finset.range_eq_Ico]
          rw [show 1 = ∑ j in Finset.Ico 0 1, p ^ j by simp]
          apply Finset.sum_Ico_consecutive
          all_goals omega

        have : (∑ j in Finset.Ico 1 m, p ^ j) = (∑ j in Finset.range m, p ^ j) - 1 := by
          exact Nat.eq_sub_of_add_eq' h_sum_two_parts

        rw [this]

      -- now we can use the geometric series formula
      _ = (p ^ m - 1) / (p - 1) - 1 - (m - 1) := by
        congr
        apply Nat.geomSum_eq (by omega)
      _ = (p ^ m - 1) / (p - 1) - m := by omega
