import Mathlib

open Finset

/- Let $n \geqslant 3$ be an integer. Prove that there exists a set $S$ of $2 n$ positive integers satisfying the following property: For every $m=2,3, \ldots, n$ the set $S$ can be partitioned into two subsets with equal sums of elements, with one of subsets of cardinality $m$.  (Iceland) -/
theorem combinatorics_23564 (n : ℕ) (hn : 3 ≤ n) :
    ∃ S : Finset ℕ, S.card = 2*n ∧
      (∀ x ∈ S, 0 < x) ∧
      (∀ m ∈ Icc 2 n, ∃ T ⊆ S, T.card = m ∧ ∑ x ∈ T, x = ∑ x ∈ S \ T, x) := by
  -- We show that one of possible examples is the set $$ S=\left\{1 \cdot 3^{k}, 2 \cdot 3^{k}: k=1,2, \ldots, n-1\right\} \cup\left\{1, \frac{3^{n}+9}{2}-1\right\} $$
  let S := (Finset.Ico 1 n).image (fun k ↦ 3 ^ k) ∪ (Finset.Ico 1 n).image (fun k ↦ 2 * 3 ^ k) ∪ {1, (3 ^ n + 9) / 2 - 1}
  use S
  -- It is readily verified that all the numbers listed above are distinct (notice that the last two are not divisible by 3 ).
  have h_le : 18 ≤ (3 ^ n + 9) / 2 := by
    have : 27 ≤ 3 ^ n := by
      trans 3 ^ 3
      · rfl
      refine Nat.pow_le_pow_of_le_right ?_ hn
      norm_num
    omega
  have h_ne : 1 ≠ (3 ^ n + 9) / 2 - 1 := by
    omega
  have h_dvd : 2 ∣ 3 ^ n + 9 := by
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    reduce_mod_char
    norm_num
    reduce_mod_char
  have h_inj3 : Function.Injective (fun k => 3 ^ k) := by
    apply Nat.pow_right_injective
    norm_num
  have h_inj23 : Function.Injective (fun k => 2 * 3 ^ k) := by
    change Function.Injective ((fun k ↦ 2 * k) ∘ (fun k ↦ 3 ^ k))
    apply Function.Injective.comp
    · apply mul_right_injective₀
      norm_num
    · exact h_inj3
  have h_disj_12 : Disjoint (image (fun k => 3 ^ k) (Ico 1 n)) (image (fun k => 2 * 3 ^ k) (Ico 1 n)) := by
    rw [Finset.disjoint_iff_ne]
    intro i hi j hj
    simp only [mem_image, mem_Ico] at hi hj
    obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := hi
    obtain ⟨y, ⟨hy1, hy2⟩, hy3⟩ := hj
    subst hx3 hy3
    intro h
    apply_fun (fun x ↦ (x : ZMod 2)) at h
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul] at h
    reduce_mod_char at h
    simp at h
  have h_disj : Disjoint (image (fun k => 3 ^ k) (Ico 1 n) ∪ image (fun k => 2 * 3 ^ k) (Ico 1 n)) {1, (3 ^ n + 9) / 2 - 1} := by
    rw [Finset.disjoint_iff_ne]
    intro i hi j hj
    simp only [mem_union, mem_image, mem_Ico, mem_insert, mem_singleton] at hi hj
    rcases hi with ⟨x, ⟨hx1, hx2⟩, hx3⟩ | ⟨x, ⟨hx1, hx2⟩, hx3⟩ <;> rcases hj with hj | hj <;> subst hx3 hj
    · suffices 3 ≤ 3 ^ x by omega
      apply Nat.le_self_pow
      omega
    · qify [show 1 ≤ (3 ^ n + 9) / 2 by omega]
      rw [Int.cast_div (by norm_cast) (by norm_num)]
      simp only [Int.cast_add, Int.cast_pow, Int.cast_ofNat, ne_eq]
      field_simp
      ring_nf
      norm_cast
      intro h
      apply_fun (fun x ↦ (x : ZMod 3)) at h
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add] at h
      reduce_mod_char at h
      rw [zero_pow (by omega), zero_pow (by omega)] at h
      norm_num at h
    · intro h
      apply_fun (fun x ↦ (x : ZMod 2)) at h
      simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_one, mul_eq_one] at h
      replace h := h.left
      reduce_mod_char at h
      simp only [zero_ne_one] at h
    · qify [show 1 ≤ (3 ^ n + 9) / 2 by omega]
      rw [Int.cast_div (by norm_cast) (by norm_num)]
      simp only [Int.cast_add, Int.cast_pow, Int.cast_ofNat, ne_eq]
      field_simp
      ring_nf
      norm_cast
      intro h
      apply_fun (fun x ↦ (x : ZMod 3)) at h
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add] at h
      reduce_mod_char at h
      rw [zero_pow (by omega), zero_pow (by omega)] at h
      norm_num at h
  constructor
  · rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_pair,
      Finset.card_image_of_injective, Finset.card_image_of_injective]
    · simp only [Nat.card_Ico]
      omega
    · exact h_inj23
    · exact h_inj3
    · exact h_ne
    · exact h_disj_12
    · exact h_disj
  constructor
  · intro x hx
    simp only [union_insert, union_assoc, mem_insert, mem_union, mem_image, mem_Ico, mem_singleton,
      S] at hx
    rcases hx with hx | ⟨y, ⟨hy1, hy2⟩, hy3⟩ | ⟨y, ⟨hy1, hy2⟩, hy3⟩ | hx
    · omega
    · rw [← hy3]
      apply Nat.pos_pow_of_pos
      norm_num
    · rw [← hy3]
      suffices 0 < 3 ^ y by omega
      apply Nat.pos_pow_of_pos
      norm_num
    · omega
  -- The sum of elements in $S$ is $$ \Sigma=1+\left(\frac{3^{n}+9}{2}-1\right)+\sum_{k=1}^{n-1}\left(1 \cdot 3^{k}+2 \cdot 3^{k}\right)=\frac{3^{n}+9}{2}+\sum_{k=1}^{n-1} 3^{k+1}=\frac{3^{n}+9}{2}+\frac{3^{n+1}-9}{2}=2 \cdot 3^{n} $$
  have h1 : ∑ x ∈ S, x = 2 * 3 ^ n := by
    simp only [S]
    rw [Finset.sum_union h_disj, Finset.sum_union h_disj_12, Finset.sum_image, Finset.sum_image, Finset.sum_pair h_ne]
    rotate_left
    · intro x hx y hy
      apply h_inj23
    · intro x hx y hy
      apply h_inj3
    qify [show 1 ≤ (3 ^ n + 9) / 2 by omega]
    rw [Int.cast_div (by norm_cast) (by norm_num)]
    simp only [Int.cast_add, Int.cast_pow, Int.cast_ofNat, add_sub_cancel]
    rw [geom_sum_Ico (by norm_num) (by omega), ← Finset.mul_sum, geom_sum_Ico  (by norm_num) (by omega)]
    norm_num
    field_simp
    ring
  -- Hence, in order to show that this set satisfies the problem requirements, it suffices to present, for every $m=2,3, \ldots, n$, an $m$-element subset $A_{m} \subset S$ whose sum of elements equals $3^{n}$.
  suffices ∀ m ∈ Icc 2 n, ∃ T ⊆ S, T.card = m ∧ ∑ x ∈ T, x = 3 ^ n by
    peel this with m hm T hTS hT_card this
    convert this
    have := Finset.sum_inter_add_sum_diff S T id
    simp only [id_eq, h1] at this
    rw [show S ∩ T = T by rwa [Finset.inter_eq_right]] at this
    linarith
  intro m hm
  simp only [mem_Icc] at hm
  -- Such a subset is $$ A_{m}=\left\{2 \cdot 3^{k}: k=n-m+1, n-m+2, \ldots, n-1\right\} \cup\left\{1 \cdot 3^{n-m+1}\right\} .$$
  let A : Finset ℕ := (Finset.Ioo (n - m) n).image (fun k ↦ 2 * 3 ^ k) ∪ {3 ^ (n - m + 1)}
  use A
  constructor
  · simp only [union_insert, union_assoc, A, S]
    apply Finset.union_subset
    · trans (image (fun k => 3 ^ k) (Ico 1 n) ∪ (image (fun k => 2 * 3 ^ k) (Ico 1 n) ∪ {(3 ^ n + 9) / 2 - 1}))
      swap
      · apply subset_insert
      trans (image (fun k => 2 * 3 ^ k) (Ico 1 n) ∪ {(3 ^ n + 9) / 2 - 1})
      swap
      · exact subset_union_right
      trans image (fun k => 2 * 3 ^ k) (Ico 1 n)
      swap
      · exact subset_union_left
      apply Finset.image_subset_image
      intro x
      simp only [mem_Ioo, mem_Ico, and_imp]
      omega
    · simp only [singleton_subset_iff, mem_insert, mem_union, mem_image, mem_Ico, Nat.ofNat_pos,
        ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, pow_right_inj₀, exists_eq_right,
        le_add_iff_nonneg_left, zero_le, true_and, mem_singleton]
      right
      left
      omega
  have h_disj : Disjoint (image (fun k => 2 * 3 ^ k) (Ioo (n - m) n)) {3 ^ (n - m + 1)} := by
    rw [Finset.disjoint_iff_ne]
    intro i hi j hj
    simp only [mem_image, mem_Ioo, mem_singleton] at hi hj
    obtain ⟨x, ⟨hx1, hx2⟩, hx3⟩ := hi
    subst hj hx3
    intro h
    apply_fun (fun x ↦ (x : ZMod 2)) at h
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at h
    reduce_mod_char at h
    simp at h
  constructor
  -- Clearly, $\left|A_{m}\right|=m$.
  · simp only [A]
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective]
    · simp only [Nat.card_Ioo, card_singleton]
      omega
    · exact h_inj23
    · apply h_disj
  -- The sum of elements in $A_{m}$ is $$ 3^{n-m+1}+\sum_{k=n-m+1}^{n-1} 2 \cdot 3^{k}=3^{n-m+1}+\frac{2 \cdot 3^{n}-2 \cdot 3^{n-m+1}}{2}=3^{n} $$
  simp only [A]
  rw [Finset.sum_union h_disj, Finset.sum_image]
  swap
  · intro x hx y hy
    apply h_inj23
  simp only [sum_singleton]
  rw [← Finset.mul_sum, ← Nat.Ico_succ_left, mul_comm]
  zify
  rw [show (2 : ℤ) = 3 - 1 by norm_num, geom_sum_Ico_mul _ (by omega)]
  simp
  -- as required.
