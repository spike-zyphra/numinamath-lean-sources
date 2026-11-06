import Mathlib

/- Let $m, n$, and $p$ be odd positive integers. Prove that the number

$$
\sum_{k=1}^{(n-1)^{p}} k^{m}
$$

is divisible by $n$. -/
theorem number_theory_607929 (m n p : ℕ) (hm : Odd m) (hn : Odd n) (hp : Odd p)
    (hpos : m > 0 ∧ n > 0 ∧ p > 0) :
    n ∣ ∑ k ∈ Finset.Icc 1 ((n - 1) ^ p), k ^ m := by
  rcases hn
  -- Since $n$ is odd, the sum has an even number of terms.
  have _2_dvd_n_sub_1 : 2 ∣ n - 1 := by omega
  obtain ⟨q, n_sub_1_pow_p_eq⟩ : 2 ∣ (n - 1) ^ p := by
    have : (n - 1) ^ p ≡ 0 [MOD 2] := by calc
      (n - 1) ^ p = (n - 1) ^ ((p - 1) + 1) := by congr; omega
      _ = (n - 1) ^ (p - 1) * (n - 1) := rfl
      _ ≡ (n - 1) ^ (p - 1) * 0 [MOD 2] := by gcongr; exact Nat.modEq_zero_iff_dvd.mpr _2_dvd_n_sub_1
      _ = 0 := by simp
    exact Nat.dvd_of_mod_eq_zero this
  /-
  So we can write it as

  $$ \sum_{k=1}^{\frac{1}{2}(n-1)^{p}}\left(k^{m}+\left((n-1)^{p}-k+1\right)^{m}\right) $$
  -/
  have sum_k_pow_m_eq : ∑ k ∈ Finset.Icc 1 ((n - 1) ^ p), k ^ m = ∑ k ∈ Finset.Icc 1 q, (k ^ m + ((n - 1) ^ p - k + 1) ^ m) :=
    suffices ∑ k ∈ Finset.Icc 1 (2 * q), k ^ m = ∑ k ∈ Finset.Icc 1 q, (k ^ m + (2 * q - k + 1) ^ m) by rw [n_sub_1_pow_p_eq]; exact this
    by calc
      ∑ k ∈ Finset.Icc 1 (2 * q), k ^ m = ∑ k ∈ Finset.Icc 1 q, k ^ m + ∑ k ∈ Finset.Icc (q + 1) (2 * q), k ^ m := by
        let left := Finset.Icc 1 q
        have left_coe_Icc := Finset.coe_Icc 1 q
        let right := Finset.Icc (q + 1) (2 * q)
        have right_coe_Icc := Finset.coe_Icc (q + 1) (2 * q)
        have disjoint : Disjoint left right := by
          apply Finset.disjoint_coe.mp --suffices Disjoint (left : Set ℕ) (right : Set ℕ) from Finset.disjoint_coe.mp this
          rw [left_coe_Icc, right_coe_Icc]
          intro x x_subset_left x_subset_right
          intro n n_in_x
          rcases x_subset_left n_in_x
          rcases x_subset_right n_in_x
          omega
        have : Finset.Icc 1 (2 * q) = left.disjUnion right disjoint := by
          apply Finset.coe_inj.mp
          rw [Finset.disjUnion_eq_union left right disjoint]
          rw [Finset.coe_union left right]
          rw [Finset.coe_Icc 1 (2 * q), left_coe_Icc, right_coe_Icc]
          apply Set.ext
          intro a
          constructor
          . intro a_in_left
            simp at a_in_left ⊢
            omega
          . intro a_in_right
            simp at a_in_right ⊢
            omega
        rw [this]
        apply Finset.sum_disjUnion
      _ = ∑ k ∈ Finset.Icc 1 q, k ^ m + ∑ k ∈ Finset.Icc 1 q, (2 * q - k + 1) ^ m := by
        congr 1
        let f n := 2 * q + 1 - n
        apply Finset.sum_bij' (fun a ha => f a) (fun a ha => f a)
        . intro a ha
          simp at ha ⊢
          unfold f
          omega
        . intro a ha
          simp at ha ⊢
          unfold f
          omega
        . intro a ha
          simp at ha ⊢
          unfold f
          omega
        . intro a ha
          simp at ha ⊢
          unfold f
          omega
        . intro a ha
          simp at ha
          unfold f
          congr
          omega
      _ = ∑ k ∈ Finset.Icc 1 q, (k ^ m + (2 * q - k + 1) ^ m) := Eq.symm Finset.sum_add_distrib

  -- So each term in the sum (1) is divisible by $n$, and so is the sum.
  have n_dvd_term : ∀ k ≤ (n - 1) ^ p, n ∣ k ^ m + ((n - 1) ^ p - k + 1) ^ m := by
    intro k _
    -- Because $m$ is odd, each term in the sum has $k+(n-1)^{p}-k+1=(n-1)^{p}+1$ as a factor.
    have dvd_1 : (n - 1) ^ p + 1 ∣ k ^ m + ((n - 1) ^ p - k + 1) ^ m := by
      rw [show (n - 1) ^ p + 1 = k + ((n - 1) ^ p - k + 1) by omega]
      exact Odd.nat_add_dvd_pow_add_pow k ((n - 1) ^ p - k + 1) hm
    -- As $p$ is odd, too, $(n-1)^{p}+1=(n-1)^{p}+1^{p}$ has $(n-1)+1=n$ as a factor.
    have dvd_2 : n ∣ (n - 1) ^ p + 1 := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      conv_rhs => rhs; rw [show 1 = 1 ^ p by simp]
      exact Odd.nat_add_dvd_pow_add_pow (n - 1) 1 hp
    exact Nat.dvd_trans dvd_2 dvd_1
  -- and so is the sum
  rw [sum_k_pow_m_eq]
  apply Finset.dvd_sum
  intro k k_in_Icc
  simp at k_in_Icc
  apply n_dvd_term
  linarith
