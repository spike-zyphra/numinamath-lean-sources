import Mathlib

namespace number_theory_97914

def Progressive (n : ℕ) (a : ℕ → ℕ) : Prop :=
  0 < a 0 ∧ (∀ i ≥ n, a i = 0) ∧ StrictMonoOn a (Finset.range n) ∧ ∀ i ∈ Finset.range (n - 1), a i ∣ a (i + 1)

end number_theory_97914

open Finset number_theory_97914

/- For $n \ge 1$ call a finite sequence $(a_1, a_2 \ldots a_n)$ of positive integers progressive if $a_i < a_{i+1}$ and $a_i$ divides $a_{i+1}$ for all $1 \le i \le n-1$. Find the number of progressive sequences such that the sum of the terms in the sequence is equal to $360$. -/
theorem number_theory_97914 :
    Set.ncard {a | ∃ n, Progressive n a ∧ ∑ i ∈ range n, a i = 360} = 47 := by
  -- let s be the set of all progressive sequences with the sum k
  set s := fun k => {a | ∃ n, Progressive n a ∧ ∑ i ∈ range n, a i = k}
  -- let sx(x, k) be the set of all progressive sequences with the sum k such that a(0) = x
  set sx := fun x k => {a | ∃ n, a 0 = x ∧ Progressive n a ∧ ∑ i ∈ range n, a i = k}
  -- let s1(k) be the set of all progressive sequences with the sum k such that a(0) > 1
  set s1 := fun k => {a | ∃ n, 1 < a 0 ∧ Progressive n a ∧ ∑ i ∈ range n, a i = k}
  -- for any progressive sequence a, we have 0 < a(i) and a(0) ≤ a(i) when i < n
  have hp_pos {n i : ℕ} {a} (ha : Progressive n a) (hi : i < n) : 0 < a i ∧ a 0 ≤ a i := by
    suffices h : a 0 ≤ a i from ⟨lt_of_lt_of_le ha.1 h, h⟩
    exact ha.2.2.1.monotoneOn (by simp; omega) (by simp; omega) (Nat.zero_le _)
  -- for any progressive sequence a, we have 0 < n
  have hn_pos {n a} (ha : Progressive n a) : 0 < n := by
    by_contra! h
    have h1 := ha.1
    have h2 := ha.2.1 0 h
    omega
  -- for any progressive sequence a, we have a(0) divides a(i)
  have hp_dvd0 {n i : ℕ} {a} (ha : Progressive n a) : a 0 ∣ a i := by
    replace ⟨ha0, h0, _, ha⟩ := ha
    -- a simple proof by induction
    induction i generalizing ha with
    | zero => rfl
    | succ i ih =>
      by_cases h : i + 1 ≥ n
      · rw [h0 (i + 1) h]
        exact Nat.dvd_zero _
      trans a i
      · exact ih ha
      · exact ha i (by simp; omega)
  -- since a(0) divides a(i), we get that a(0) divides the sum of a
  have hp_dvd_sum {n : ℕ} {a} (ha : Progressive n a) : a 0 ∣ ∑ i ∈ range n, a i := by
    apply dvd_sum
    simp only [mem_range]
    intro i _
    exact hp_dvd0 ha
  -- n * a(0) is a lower bounds of the sum of a progressive sequence a(i)
  have hsum_bound {n a} (ha : Progressive n a) : n * a 0 ≤ ∑ i ∈ range n, a i := by
    have h := Finset.card_nsmul_le_sum (range n) a (a 0)
    simp only [mem_range, card_range, smul_eq_mul] at h
    apply h
    intro i hi
    exact (hp_pos ha hi).2
  -- sx(x, k1) and sx(y, k2) are disjoint when x ≠ y
  have hsx_disj {x y k1 k2} (hxy : x ≠ y) : Disjoint (sx x k1) (sx y k2) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext a
    simp only [exists_and_left, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_and, not_exists, and_imp, forall_exists_index, sx]
    intro ha0
    simp [ha0, hxy]
  -- sx(1, k1) and s1(k2) are disjoint (since s1 contains sequences with a(0) > 1)
  have hsx1_disj {k1 k2} : Disjoint (sx 1 k1) (s1 k2) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext a
    simp only [exists_and_left, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_and, not_exists, and_imp, forall_exists_index, sx, s1]
    intro ha0
    simp [ha0]
  -- we prove that |sx(x, k)| = |s1(k / x - 1)| (where |·| is the cardinality of a set)
  have hsx_eq {x k} (hx : 0 < x) (hk : x < k) (hxk : x ∣ k) : (sx x k).encard = (s1 (k / x - 1)).encard := by
    -- it is enough to show that sx(x, k) is an injective image of s1(k / x - 1):
    -- for every sequence b(i) ∈ s1(k / x - 1) consider another sequence a(i) defined by
    -- a(0) = x and a(i) = x * b(i - 1)
    suffices eq : sx x k = (fun a i => if i = 0 then x else x * a (i - 1)) '' s1 (k / x - 1) by
      rw [eq, Set.InjOn.encard_image]
      intro a
      simp only [exists_and_left, Set.mem_setOf_eq, and_imp, forall_exists_index, s1]
      intro _ _ _ _ b _ _ _ _ eq
      ext i
      have := congr_fun eq (i + 1)
      simp [show i + 1 ≠ 0 by omega, show x ≠ 0 by omega] at this
      exact this
    ext a
    simp only [exists_and_left, Set.mem_setOf_eq, Set.mem_image, sx, s1]
    constructor
    · intro ⟨ha0, n, ha, hsum⟩
      -- suppose that a(i) is progressive with the sum k and show that b(i) is progressive
      -- with the sum k / x - 1
      have hn : 2 ≤ n := by
        contrapose! hsum
        interval_cases n <;> simp [ha0] <;> omega
      have hx_dvd i : x ∣ a i := by rw [←ha0]; exact hp_dvd0 ha
      use fun i => a (i + 1) / x
      -- use facts that 2 ≤ n and x divides a(i) for all i and
      -- check all properties of a progressive sequence
      constructorm* _ ∧ _
      · rw [Nat.lt_div_iff_mul_lt' (hx_dvd 1), mul_one, ←ha0]
        exact ha.2.2.1 (by simp; omega) (by simp; omega) zero_lt_one
      · use n - 1
        constructor
        · dsimp [Progressive]
          constructorm* _ ∧ _
          · apply Nat.div_pos _ hx
            rw [←ha0]
            exact (hp_pos ha (by omega)).2
          · intro i hi
            rw [ha.2.1 (i + 1) (by omega), Nat.zero_div]
          · simp only [StrictMonoOn, coe_range, Set.mem_Iio]
            intro i hi j hj hij
            apply Nat.div_lt_div_of_lt_of_dvd (hx_dvd _)
            exact ha.2.2.1 (by simp; omega) (by simp; omega) (by omega)
          · simp only [mem_range]
            intro i hi
            rw [Nat.dvd_div_iff_mul_dvd (hx_dvd _), Nat.mul_div_cancel' (hx_dvd _)]
            exact ha.2.2.2 (i + 1) (by simp; omega)
        · rw [←hsum]
          apply Nat.eq_of_mul_eq_mul_left hx
          rw [Finset.mul_sum, Nat.mul_sub, Nat.mul_div_cancel' (by rw [←ha0]; exact hp_dvd_sum ha)]
          nth_rw 2 [show n = (n - 1) + 1 by omega]
          rw [sum_range_succ', ha0, mul_one, add_tsub_cancel_right]
          apply sum_congr rfl
          intro i _
          rw [Nat.mul_div_cancel' (hx_dvd _)]
      · ext i
        split_ifs with h
        · rw [h, ha0]
        · rw [show i - 1 + 1 = i by omega, Nat.mul_div_cancel' (hx_dvd i)]
    · intro ⟨b, ⟨hb0, n, hb, hsum⟩, eq⟩
      -- suppose that b(i) is a progressive sequence with the sum k / x - 1
      -- and show that a(i) is progressive with the sum k
      simp [←eq]
      use n + 1
      constructor
      · simp [Progressive, hx]
        constructorm* _ ∧ _
        · intro i hi
          simp [show i ≠ 0 by omega]
          right
          exact hb.2.1 (i - 1) (by omega)
        · simp only [StrictMonoOn, Set.mem_Iio]
          intro i hi j hj hij
          split_ifs <;> try omega
          · nth_rw 1 [←mul_one x]
            apply Nat.mul_lt_mul_of_pos_left _ hx
            apply lt_of_lt_of_le hb0
            exact (hp_pos hb (by omega)).2
          · apply Nat.mul_lt_mul_of_pos_left _ hx
            apply hb.2.2.1 (by simp; omega) (by simp; omega) (by omega)
        · intro i hi
          split_ifs
          use b i
          apply Nat.mul_dvd_mul_left
          nth_rw 2 [show i = i - 1 + 1 by omega]
          exact hb.2.2.2 (i - 1) (by simp; omega)
      · simp [sum_range_succ', ←mul_sum, hsum, Nat.mul_sub, Nat.mul_div_cancel' hxk]
        omega
  -- it is easy to show that the set s1(1) is empty, so |s1(1)| = 0
  have hs1_0 : (s1 1).encard = 0 := by
    rw [Set.encard_eq_zero]
    ext a
    simp only [exists_and_left, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
      not_exists, s1]
    intro ha0 n ha h
    have h1 := hsum_bound ha
    have hn := hn_pos ha
    contrapose! h1
    rw [h, Nat.one_lt_mul_iff]
    omega
  -- the set sx(x, x) contains only one sequence defined by a(0) = x, a(i) = 0 for i > 0
  -- so |sx(x, x)| = 1
  have hsx1 {x} (hx : 0 < x) : (sx x x).encard = 1 := by
    rw [Set.encard_eq_one]
    use fun i => if i = 0 then x else 0
    ext a
    simp only [exists_and_left, Set.mem_setOf_eq, Set.mem_singleton_iff, sx]
    constructor
    · intro ⟨ha0, n, ha, hsum⟩
      have hn : n = 1 := by
        have h := hsum_bound ha
        rw [ha0, hsum] at h
        nth_rw 2 [← one_mul x] at h
        replace h := Nat.le_of_mul_le_mul_right h hx
        interval_cases n <;> [skip; rfl]
        simp at hsum
        omega
      ext i
      split_ifs with hi
      · rw [hi, ha0]
      · exact ha.2.1 i (by omega)
    · simp only [Progressive, ge_iff_le, StrictMonoOn, coe_range, Set.mem_Iio, mem_range]
      intro h
      simp [h]
      use 1
      simp [hx]
      intro i _
      omega
  -- we have s(k) = sx(1, k) ∪ s1(k)
  -- so |s(k)| = |sx(1, k)| + |s1(k)| = |s1(k / 1 - 1)| + |s1(k)| (when 1 < k)
  have hs_eq {k} (hk : 1 < k) : (s k).encard = (s1 k).encard + (s1 (k - 1)).encard := by
    suffices eq : s k = sx 1 k ∪ s1 k by
      rw [eq, Set.encard_union_eq hsx1_disj, hsx_eq zero_lt_one hk (Nat.one_dvd _)]
      rw [Nat.div_one, add_comm]
    ext a
    simp only [Set.mem_setOf_eq, exists_and_left, Set.mem_union, s, sx, s1]
    constructor
    · intro ⟨n, ha⟩
      by_cases h : a 0 = 1
      · left
        simp [h]
        use n
      · right
        have := ha.1.1
        simp [show 1 < a 0 by omega]
        use n
    · intro h
      rcases h with ⟨ha0, n, h⟩ | ⟨ha0, n, h⟩ <;> use n
  -- derive a formula for |s1(k)|
  -- we have s1(k) = ⋃ x, sx(x, k) where the union is taken over all possible values of a(0)
  -- we know that a(0) divides k and that 1 < a(0), so we can take the union over
  -- all divisors of k excluding 1
  -- we also have |sx(k, k)| = 1 so take the sum of cardinalities over all proper divisors of k without 1
  -- and add 1 to the result
  have hs1_eq {k} (hk : 1 < k) : (s1 k).encard = 1 + ∑ d ∈ k.properDivisors \ {1}, (s1 (k / d - 1)).encard := by
    -- first, show that s1(k) = sx(k, k) ∪ ⋃ d ∈ k.properDivisors \ {1}, sx(d, k)
    have eq : s1 k = sx k k ∪ ⋃ d ∈ k.properDivisors \ {1}, sx d k := by
      ext a
      simp only [exists_and_left, Set.mem_setOf_eq, mem_sdiff, Nat.mem_properDivisors,
        mem_singleton, Set.mem_union, Set.mem_iUnion, exists_prop, exists_eq_left', s1, sx]
      constructor
      · intro ⟨ha0, n, ha, hsum⟩
        by_cases h : a 0 = k
        · left
          simp [h]
          use n
        · right
          have hs := hsum_bound ha
          rw [hsum] at hs
          have hak : a 0 ≤ k := calc
            a 0 ≤ k / n := by
              rw [mul_comm, ← Nat.le_div_iff_mul_le (hn_pos ha)] at hs
              exact hs
            _ ≤ k := Nat.div_le_self _ _
          simp_rw [and_assoc]
          exact ⟨by rw [←hsum]; exact hp_dvd_sum ha, by omega, by omega, n, ha, hsum⟩
      · intro h
        rcases h with ⟨ha0, h⟩ | ⟨ha0, n, ha, hsum⟩
        · exact ⟨by omega, h⟩
        · have := ha.1
          exact ⟨by omega, n, ha, hsum⟩
    -- we get |s1(k)| = |sx(k, k)| + |⋃ d, sx(d, k)| = 1 + |⋃ d, sx(d, k)|
    rw [eq, Set.encard_union_eq, hsx1 (by omega)]
    pick_goal 2
    · simp only [mem_sdiff, Nat.mem_properDivisors, mem_singleton, Set.disjoint_iUnion_right,
        and_imp]
      intro x _ hxk _
      apply hsx_disj (ne_of_gt hxk)
    congr
    -- show that |⋃ d, sx(d, k)| = ∑ d, |sx(d, k)| (it follows from the fact that sx(d1, k) and sx(d2, k) are disjoint)
    have h (r : Finset ℕ) : (⋃ d ∈ r, sx d k).encard = ∑ d ∈ r, (sx d k).encard := by
      induction r using Finset.induction with
      | empty => simp
      | @insert x r hxr ih =>
        simp only [mem_insert, Set.iUnion_iUnion_eq_or_left]
        rw [Set.encard_union_eq, ih, sum_insert hxr]
        simp only [Set.disjoint_iUnion_right]
        intro y hy
        apply hsx_disj
        contrapose! hxr
        simp [hxr, hy]
    rw [h]
    apply sum_congr rfl
    -- it is left to show that |sx(d, k)| = |s1(k / x - 1)| which follows
    -- from results proven above
    simp only [mem_sdiff, Nat.mem_properDivisors, mem_singleton, and_imp]
    intro x hxk hxk2 hx1
    have hx_pos : 0 < x := by
      contrapose! hxk
      rw [show x = 0 by omega, Nat.zero_dvd]
      omega
    rw [hsx_eq hx_pos hxk2 hxk]
  -- a corollary of the previous result is that
  -- |s1(k)| = 1 for prime k (the only proper divisor of a prime k is 1)
  have hs1p_eq k (hk : k.Prime) : (s1 k).encard = 1 := by simp [hs1_eq hk.one_lt, hk.properDivisors]
  -- it is left to show that |s(360)| = 47
  suffices (s 360).encard = 47 by simp only [Set.ncard_def, this, ENat.toNat_ofNat]
  -- |s(360)| = |s1(360)| + |s1(359)|
  rw [hs_eq (by norm_num), hs1_eq (by norm_num)]
  -- 359 is prime, so |s1(359)| = 1
  rw [hs1p_eq (360 - 1) (by norm_num)]
  -- consider all proper divisors of 360
  rw [show Nat.properDivisors 360 \ {1} = {2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45, 60, 72, 90, 120, 180} by decide]
  simp only [mem_insert, Nat.reduceEqDiff, mem_singleton, or_self, not_false_eq_true, sum_insert,
    Nat.reduceDiv, Nat.add_one_sub_one, sum_singleton, hs1_0]
  -- |s1(p)| = 1 for all prime numbers p
  rw [hs1p_eq 179 (by norm_num), hs1p_eq 89 (by norm_num), hs1p_eq 71 (by norm_num)]
  rw [hs1p_eq 59 (by norm_num), hs1p_eq 29 (by norm_num), hs1p_eq 23 (by norm_num)]
  rw [hs1p_eq 19 (by norm_num), hs1p_eq 17 (by norm_num), hs1p_eq 11 (by norm_num)]
  -- use similar computations to establish the final result
  rw [hs1_eq (by norm_num), show Nat.properDivisors 119 \ {1} = {7, 17} by decide]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 44 \ {1} = {2, 4, 11, 22} by decide]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 39 \ {1} = {3, 13} by decide]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 35 \ {1} = {5, 7} by decide]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 14 \ {1} = {2, 7} by decide]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 9 \ {1} = {3} by decide]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 8 \ {1} = {2, 4} by decide]
  simp [hs1_0, hs1p_eq 3 (by norm_num), hs1p_eq 2 (by norm_num)]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 16 \ {1} = {2, 4, 8} by decide]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 6 \ {1} = {2, 3} by decide]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 21 \ {1} = {3, 7} by decide]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 10 \ {1} = {2, 5} by decide]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 12 \ {1} = {2, 3, 4, 6} by decide]
  simp [hs1_0, hs1p_eq 7 (by norm_num), hs1p_eq 5 (by norm_num), hs1p_eq 3 (by norm_num), hs1p_eq 2 (by norm_num)]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 6 \ {1} = {2, 3} by decide]
  rw [hs1_eq (by norm_num), show Nat.properDivisors 4 \ {1} = {2} by decide]
  simp [hs1_0, hs1p_eq 2 (by norm_num)]
  norm_num