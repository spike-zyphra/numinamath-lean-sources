import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Show that for  $n \geq 5$ , the integers  $1, 2, \ldots n$  can be split into two groups so that the sum of the integers in one group equals the product of the integers in the other group.-/
theorem number_theory_8697 (n : ℕ) (hn : 5 ≤ n) :
  ∃ s t : Finset ℕ, s ∪ t = Finset.Icc 1 n ∧ s ∩ t = ∅ ∧ ∑ x ∈ s, x = ∏ y ∈ t, y := by
  -- 2k/2 = k
  have mul_div_two (k : ℕ) : (2 * k) / 2 = k := by simp
  -- 2k-2 = 2(k-1)
  have two_mul_sub_two (k : ℕ) (hk : 1 ≤ k) : 2*k-2=2*(k-1) := by
    zify
    rw [Nat.cast_sub (by linarith), Nat.cast_sub (by linarith)]
    push_cast
    ring
  -- Sum of {a,b,c} is a+b+c
  have sum_triplet {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      ∑ x ∈ {a, b, c}, x = a + b + c := by
    rw [Finset.sum_insert, Finset.sum_pair, Nat.add_assoc]
    . exact hbc
    intro ha
    simp at ha
    exact ha.elim (fun hab => by contradiction) (fun hac => by contradiction)
  -- Production of {a,b,c} is a*b*c
  have prod_triplet {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
      ∏ x ∈ {a, b, c}, x = a * b * c := by
    rw [Finset.prod_insert, Finset.prod_pair, Nat.mul_assoc]
    . exact hbc
    intro ha
    simp at ha
    exact ha.elim (fun hab => by contradiction) (fun hac => by contradiction)
  -- Finset `t` filtered by membership of subset `s` is exactly `s`.
  have filter_subset {s t : Finset ℕ} (hst : s ⊆ t) : t.filter (· ∈ s) = s := by
    ext x
    simp
    intro hxs
    exact hst hxs
  -- The collection of elements in `t` but not in `s` is exactly `t \ s`.
  have filter_not_subset {s t : Finset ℕ} (hst : s ⊆ t) : t.filter (¬ · ∈ s) = t \ s := by
    ext x
    simp
  rcases Nat.even_or_odd n with heven | hodd
  -- If  $n$  is even, use  $\left\{1,\frac{n-2}{2},n\right\}$  as the product;
  -- the sum is $$ \frac{n(n+1)-2-(n-2)-2n}{2}=\frac{n(n-2)}{2}. $$
  . set t₀ : Finset ℕ := {1, (n - 2)/2, n} with ht₀
    set t : Finset ℕ := Finset.Icc 1 n |>.filter (· ∈ t₀) with ht
    set s : Finset ℕ := Finset.Icc 1 n |>.filter (¬ · ∈ t₀) with hs
    use s, t
    have s_union_t : s ∪ t = Finset.Icc 1 n := by
      rw [Finset.union_comm]
      apply Finset.filter_union_filter_neg_eq
    have s_inter_t : s ∩ t = ∅ := by
      rw [Finset.inter_comm]
      have := Finset.disjoint_filter_filter_neg (Finset.Icc 1 n) (Finset.Icc 1 n) (fun x ↦ x ∉ t₀)
      aesop
    refine ⟨s_union_t, s_inter_t, ?_⟩
    have := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := id)
    simp [s_union_t, s_inter_t] at this
    rw [← add_left_inj (∑ x ∈ t, x), ← this]
    have : t₀ ⊆ Finset.Icc 1 n := by
      intro x
      simp [ht₀]
      intro hx
      rcases hx with hx | hx | hx
      . rw [hx]; exact ⟨by linarith, by linarith⟩
      . rw [hx]
        rcases heven with ⟨k, rfl⟩
        rw [← two_mul, two_mul_sub_two k (by linarith), mul_div_two]
        have : 2 ≤ k := by linarith
        rw [show k = k-1+1 by rw [Nat.sub_add_cancel (by linarith)]] at this
        have : k ≤ 2*k+1 := by linarith
        nth_rw 1 [show k=k-1+1 by rw [Nat.sub_add_cancel (by linarith)]] at this
        exact ⟨by linarith, by linarith⟩
      . rw [hx]
        exact ⟨by linarith, le_refl _⟩
    rw [ht, filter_subset this, ht₀]
    have one_ne_half : 1 ≠ (n - 2) / 2 := by
      rcases heven with ⟨k, rfl⟩
      rw [← two_mul, two_mul_sub_two k (by linarith), mul_div_two]
      intro h
      apply_fun (· + 1) at h
      rw [Nat.sub_add_cancel (by linarith), show 1+1=2 by norm_num] at h
      rw [← h] at hn
      norm_num at hn
    have one_ne_n : 1 ≠ n := by
      intro h
      rw [← h] at hn
      norm_num at hn
    have half_ne_n : (n - 2) / 2 ≠ n := by
      rcases heven with ⟨k, rfl⟩
      rw [← two_mul, two_mul_sub_two k (by linarith), mul_div_two]
      intro h
      apply_fun (· + 1) at h
      rw [Nat.sub_add_cancel (by linarith)] at h
      linarith
    rw [prod_triplet one_ne_half one_ne_n half_ne_n,
      sum_triplet one_ne_half one_ne_n half_ne_n]
    calc ∑ x ∈ Finset.Icc 1 n, x
    _ = ∑ x ∈ Finset.Ico 1 (n+1), x := by
      apply Finset.sum_congr
      rw [Nat.Ico_succ_right]
      simp
    _ = ∑ x ∈ Finset.range n, (x + 1) := by
      simp [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, Nat.add_comm]
    _ = ∑ x ∈ Finset.range (n + 1), x := by
      rw [Finset.sum_range_succ', Nat.add_zero]
    _ = n*(n+1)/2 := by
      rw [Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]
    _ = _ := by
      rcases heven with ⟨k, rfl⟩
      rw [← two_mul, mul_assoc, mul_div_two, two_mul_sub_two k (by linarith), mul_div_two]
      zify
      rw [Nat.cast_sub (by linarith)]
      ring
  -- If  $n$  is odd, use  $\left\{1,\frac{n-1}{2},n-1\right\}$  as the product;
  -- the sum is $$ \frac{n(n+1)-2-(n-1)-2(n-1)}{2}=\frac{(n-1)^2}{2}. $$
  set t₀ : Finset ℕ := {1, (n - 1)/2, n - 1} with ht₀
  set t : Finset ℕ := Finset.Icc 1 n |>.filter (· ∈ t₀) with ht
  set s : Finset ℕ := Finset.Icc 1 n |>.filter (¬ · ∈ t₀) with hs
  use s, t
  have s_union_t : s ∪ t = Finset.Icc 1 n := by
    rw [Finset.union_comm]
    apply Finset.filter_union_filter_neg_eq
  have s_inter_t : s ∩ t = ∅ := by
    rw [Finset.inter_comm]
    have := Finset.disjoint_filter_filter_neg (Finset.Icc 1 n) (Finset.Icc 1 n) (fun x ↦ x ∉ t₀)
    aesop
  refine ⟨s_union_t, s_inter_t, ?_⟩
  have := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := id)
  simp [s_union_t, s_inter_t] at this
  rw [← add_left_inj (∑ x ∈ t, x), ← this]
  have : t₀ ⊆ Finset.Icc 1 n := by
    intro x
    simp [ht₀]
    intro hx
    rcases hx with hx | hx | hx
    . rw [hx]; exact ⟨by linarith, by linarith⟩
    . rw [hx]
      rcases hodd with ⟨k, rfl⟩
      rw [Nat.add_sub_cancel, mul_div_two]
      exact ⟨by linarith, by linarith⟩
    . rw [hx]
      have : 2 ≤ n := by linarith
      rw [show n=n-1+1 by rw [Nat.sub_add_cancel (by linarith)]] at this
      exact ⟨by linarith, by exact sub_le n 1⟩
  rw [ht, filter_subset this, ht₀]
  have one_ne_half : 1 ≠ (n - 1) / 2 := by
    rcases hodd with ⟨k, rfl⟩
    rw [Nat.add_sub_cancel, mul_div_two]
    intro hk
    rw [← hk] at hn
    simp at hn
  have one_ne_sub : 1 ≠ n - 1 := by
    intro h
    apply_fun (· + 1) at h
    rw [Nat.sub_add_cancel (by linarith), show 1+1=2 by norm_num] at h
    rw [← h] at hn
    norm_num at hn
  have half_ne_sub : (n - 1) / 2 ≠ n - 1 := by
    rcases hodd with ⟨k, rfl⟩
    rw [Nat.add_sub_cancel, mul_div_two]
    intro hk
    nth_rw 1 [← one_mul k] at hk
    have : 0 < k := by linarith
    have := Nat.mul_right_cancel this hk
    norm_num at this
  rw [prod_triplet one_ne_half one_ne_sub half_ne_sub,
    sum_triplet one_ne_half one_ne_sub half_ne_sub]
  calc ∑ x ∈ Finset.Icc 1 n, x
    _ = ∑ x ∈ Finset.Ico 1 (n+1), x := by
      apply Finset.sum_congr
      rw [Nat.Ico_succ_right]
      simp
    _ = ∑ x ∈ Finset.range n, (x + 1) := by
      simp [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, Nat.add_comm]
    _ = ∑ x ∈ Finset.range (n + 1), x := by
      rw [Finset.sum_range_succ', Nat.add_zero]
    _ = n*(n+1)/2 := by
      rw [Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]
    _ = _ := by
      rcases hodd with ⟨k, rfl⟩
      rw [Nat.add_sub_cancel, mul_div_two, show 2*k+1+1=2*(k+1) by ring,
        ← mul_assoc, mul_comm _ 2, mul_assoc, mul_div_two]
      ring
