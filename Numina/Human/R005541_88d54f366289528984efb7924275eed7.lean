import Mathlib

/-Justine has a coin which will come up the same as the last flip $\frac{2}{3}$ of the time and the other side $\frac{1}{3}$ of the time. She flips it and it comes up heads. She then flips it 2010 more times. What is the probability that the last flip is heads?-/
theorem combinatorics_608740 (n : ℕ) (hn : n = 2010) :
    ∑ i ∈ Finset.range (n + 1), n.choose (2 * i) * (1 / 3 : ℝ)^(2 * i) * (2 / 3 : ℝ)^(n - 2 * i) = (3^n + 1) / (2 * 3^n) := by
  -- Define probabilities $p$ and $q$ for same and different flips.
  let q := (1 / 3 : ℝ)
  let p := (2 / 3 : ℝ)
  have hpq : p + q = 1 := by norm_num
  have hpmq : -q + p = q := by norm_num
  -- Define the total sum over all possible number of changes.
  let sum_all := ∑ k ∈ Finset.range (n + 1), (n.choose k) * q ^ k * p ^ (n - k)
  have h_all : sum_all = 1 := by
    unfold sum_all
    conv_lhs =>
      congr
      · rfl
      · ext k
        rw [mul_assoc,mul_comm]
    rw [← add_pow q p n]
    rw [add_comm, hpq]
    exact one_pow n
  -- Define the signed sum for alternating changes.
  let sum_signed := ∑ k ∈ Finset.range (n + 1), (n.choose k) * (-q) ^ k * p ^ (n - k)
  have h_signed : sum_signed = q ^ n := by
    unfold sum_signed
    conv_lhs =>
      congr
      · rfl
      · ext k
        rw [mul_assoc, mul_comm]
    rw [← add_pow (-q) p n]
    rw [hpmq]
  -- Partition the terms into even and odd number of changes.
  let S_even := Finset.filter (fun k => Even k) (Finset.range (n + 1))
  let S_odd := Finset.filter (fun k => ¬Even k) (Finset.range (n + 1))
  have h_disj : Disjoint S_even S_odd := Finset.disjoint_filter_filter_neg (Finset.range (n + 1)) (Finset.range (n + 1)) Even
  have h_union : S_even ∪ S_odd = Finset.range (n + 1) := Finset.filter_union_filter_neg_eq (Even) (Finset.range (n + 1))
  let term := fun k => (n.choose k) * q ^ k * p ^ (n - k)
  have h_all' : sum_all = ∑ k ∈ S_even, term k + ∑ k ∈ S_odd, term k := by
    rw [← Finset.sum_union h_disj]
    rw [h_union]
  -- Express the signed sum in terms of even and odd parts.
  have h_signed' : sum_signed = ∑ k ∈ S_even, term k - ∑ k ∈ S_odd, term k := by
    unfold sum_signed
    have h_term_signed : ∀ k ∈ Finset.range (n + 1), (n.choose k) * (-q) ^ k * p ^ (n - k) = ((-1) ^ k) * term k := by
      intro k _
      unfold term
      rw [neg_pow q k ]
      conv_lhs =>
        congr
        · rw [mul_left_comm (n.choose k : ℝ) ((-1) ^ k) (q ^ k)]
        · skip
      rw [mul_assoc ((-1) ^ k) ((n.choose k : ℝ) * q ^ k) (p ^ (n - k))]
    rw [Finset.sum_congr rfl h_term_signed]
    rw [← h_union]
    rw [Finset.sum_union h_disj]
    have h_even_sign : ∀ k ∈ S_even, (-1 : ℝ) ^ k = 1 := by
      intro k hk
      obtain ⟨_, heven⟩ := Finset.mem_filter.mp hk
      exact (neg_one_pow_eq_one_iff_even (by nlinarith)).mpr heven
    have h_odd_sign : ∀ k ∈ S_odd, (-1 : ℝ) ^ k = -1 := by
      intro k hk
      obtain ⟨_, hodd⟩ := Finset.mem_filter.mp hk
      simp [neg_one_pow_eq_ite, (by norm_num: 1 ≠ (-1 : ℝ)) ]
      exact Nat.not_even_iff_odd.mp hodd
    rw [Finset.sum_congr rfl (fun k hk => congr_arg (· * term k) (h_even_sign k hk))]
    rw [Finset.sum_congr rfl (fun k hk => congr_arg (· * term k) (h_odd_sign k hk))]
    rw [Finset.sum_congr rfl (fun k hk => mul_comm 1 (term k))]
    rw [Finset.sum_congr rfl (fun k hk => mul_comm (-1) (term k))]
    simp
    rfl
  -- Calculate the sum over even terms as average of total and signed sums.
  have h_even_term : ∑ k ∈ S_even, term k = (sum_all + sum_signed) / 2 := by
    rw [h_all', h_signed']
    ring
  -- Prove the left-hand side is the sum over even terms using bijection.
  have h_left : ∑ i ∈ Finset.range (n + 1), n.choose (2 * i) * q ^ (2 * i) * p ^ (n - 2 * i) = ∑ k ∈ S_even, term k := by
    let m := n / 2 + 1
    let dom := Finset.range m
    let f : ∀ i ∈ dom, ℕ := fun i _ => 2 * i
    have h_inj : ∀ a ha b hb, f a ha = f b hb → a = b := fun _ _ _ _ h => (Nat.mul_right_inj (show 2 ≠ 0 by decide)).mp h
    have h_map : ∀ i hi, f i hi ∈ S_even := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range]
      constructor
      · have : i < m := Finset.mem_range.1 hi
        have : i ≤ m - 1 := Nat.le_pred_of_lt this
        have : 2 * i ≤ 2 * (m - 1) := Nat.mul_le_mul_left 2 this
        have : 2 * (m - 1) = n := by omega
        have : f i hi ≤  2 * (m - 1) := by tauto
        nlinarith
      · exact even_two_mul i
    have h_surj : ∀ k ∈ S_even, ∃ i hi, f i hi = k := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range, Even] at hk
      obtain ⟨hkr, hke⟩ := hk
      let i := k / 2
      have h_2i : k = 2 * i := by omega
      have h_dvd2 : 2 ∣ k := by tauto
      have hi : i < m := by omega
      use i, Finset.mem_range.2 hi
      exact Nat.mul_div_cancel' h_dvd2
    have h_eq : ∀ i hi, term (f i hi) = n.choose (2 * i) * q ^ (2 * i) * p ^ (n - 2 * i) := fun _ _ => rfl
    have h_zero : ∀ i ∈ Finset.range (n + 1) \ dom, n.choose (2 * i) * q ^ (2 * i) * p ^ (n - 2 * i) = 0 := by
      intro i hi
      simp at hi
      rw [Finset.mem_range] at hi
      have : n < 2 * i := by omega
      rw [Nat.choose_eq_zero_of_lt this]
      ring
    have h_subset : dom ⊆ Finset.range (n + 1) := Finset.range_subset.mpr (by omega)
    rw [← Finset.sum_sdiff h_subset]
    rw [Finset.sum_eq_zero h_zero]
    rw [zero_add]
    exact Finset.sum_bij f h_map h_inj h_surj h_eq
  -- Substitute to obtain the final result.
  rw [h_left, h_even_term, h_all, h_signed]
  rw [← Real.rpow_natCast (1 / 3) n]
  field_simp
  have : (2 : ℝ) * 3 ^ n = 3 ^ n * 2 := by rw [mul_comm]
  exact Or.inl this
