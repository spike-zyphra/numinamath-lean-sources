import Mathlib

open Real

/- For a real number $x$ let $\lfloor x\rfloor$ be the greatest integer less than or equal to $x$, and define $\{x\} = x - \lfloor x \rfloor$ to be the fractional part of $x$. For example, $\{3\} = 0$ and $\{4.56\} = 0.56$. Define $f(x)=x\{x\}$, and let $N$ be the number of real-valued solutions to the equation $f(f(f(x)))=17$ for $0\leq x\leq 2020$. Find the remainder when $N$ is divided by $1000$. -/
theorem algebra_98267 {f : ℝ → ℝ} (hf : ∀ x, f x = x * (x - ⌊x⌋)) :
    {x | 0 ≤ x ∧ x ≤ 2020 ∧ f (f (f x)) = 17}.ncard % 1000 = 10 := by
  -- It is enough to show that the cardinality of the set is equal to Nat.choose 2005 3.
  suffices {x | 0 ≤ x ∧ x ≤ 2020 ∧ f (f (f x)) = 17}.encard = Nat.choose 2005 3 by
    rw [Set.ncard.eq_1, this, ENat.toNat_coe]
    rw [Nat.choose_eq_descFactorial_div_factorial]
    rw [show Nat.factorial 3 = 6 from rfl]
    -- Nat.choose 2005 3 = 2005 * 2004 * 2003 / 6 = 2005 * 334 * 2003, so
    -- Nat.choose 2005 3 % 1000 = 5 * 334 * 3 % 1000 = 5010 % 1000 = 10.
    norm_num
  -- f(x) is non-negative for all 0 ≤ x.
  have hf_nonneg x (hx : 0 ≤ x) : 0 ≤ f x := by
    rw [hf, ← Int.fract.eq_1]
    exact mul_nonneg hx (Int.fract_nonneg x)
  -- f(x) ≤ x for all 0 ≤ x.
  have hf_le x (hx : 0 ≤ x) : f x ≤ x := by
    -- f(x) = x * {x} (where {x} is the fractional part of x) and {x} < 1 so f(x) ≤ x.
    rw [hf, ← Int.fract.eq_1]
    nth_rw 3 [← mul_one x]
    gcongr
    exact le_of_lt (Int.fract_lt_one x)
  -- Define r(k, y) = (k + √(k^2 + 4y)) / 2 for k ∈ ℕ and y ∈ ℝ.
  set r : ℕ → ℝ → ℝ := fun k y => (k + √(k^2 + 4 * y)) / 2
  -- Show that k < r(k, y) when 0 < y.
  have hr1 {k y} (hy : 0 < y) : k < r k y := by
    rw [lt_div_iff₀ zero_lt_two, add_comm, ← sub_lt_iff_lt_add, show k * (2 : ℝ) - k = k by ring]
    rw [lt_sqrt (by positivity)]
    linarith
  -- Assume that 0 ≤ y and show that r(k, y) < k + 1 iff y < k + 1.
  have hr2 {k y} (hy : 0 ≤ y) : r k y < k + 1 ↔ y < k + 1 := by
    rw [div_lt_iff₀ zero_lt_two]
    rw [show ∀ y : ℝ, k + y < (k + 1) * 2 ↔ y < k + 2 by intros; constructor <;> (intros; linarith)]
    rw [sqrt_lt (by positivity) (by positivity)]
    constructor <;> (intro h; linarith)
  -- Prove that the equation f(x) = y has at most one solution for
  -- x ∈ [k, k + 1). More precisely, if x ∈ [k, k + 1) then f(x) = y has one solution
  -- x = r(k, y) when y < k + 1 and has no solutions when k + 1 ≤ y.
  have hsol1 (k : ℕ) (y : ℝ) (hy : 0 < y) : {x : ℝ | k ≤ x ∧ x < k + 1 ∧ f x = y} =
        (if k + 1 ≤ y then (∅ : Set ℝ) else {r k y}) := calc
    -- Rewrite the equation f(x) = y as x^2 - k * x - y = 0.
    -- This result follows from f(x) = x * (x - ⌊x⌋) = x * (x - k) for x ∈ [k, k + 1).
    {x : ℝ | k ≤ x ∧ x < k + 1 ∧ f x = y} = {x : ℝ | k ≤ x ∧ x < k + 1 ∧ 1 * (x * x) + (-k) * x + (-y) = 0} := by
        ext x
        simp only [Set.mem_setOf_eq, neg_mul, and_congr_right_iff, hf]
        intro hx1 hx2
        rw [show ⌊x⌋ = k by simp [Int.floor_eq_iff, hx1, hx2]]
        rw [← sub_eq_zero, Int.cast_natCast]
        ring_nf
    -- The equation x^2 - k * x - y = 0 has two solutions:
    -- x = (k ± √(k ^ 2 + 4 * y)) / 2.
    -- But only x = r(k, y) satisfies k ≤ x.
    _ = {x : ℝ | k ≤ x ∧ x < k + 1 ∧ x = r k y} := by
        ext x
        simp only [Set.mem_setOf_eq, and_congr_right_iff, r]
        intro hx1 hx2
        set d := discrim (1 : ℝ) (-k) (-y)
        have hd : d = k^2 + 4 * y := by simp [d, discrim]
        have hd0 : 0 ≤ d := by rw [hd]; positivity
        have eq : d = √d * √d := by rw [← pow_two, sq_sqrt hd0]
        rw [quadratic_eq_zero_iff one_ne_zero eq, ← hd]
        simp
        intro hx
        by_cases hd' : d = 0
        · simp [hx, hd']
        contrapose! hx1
        rw [hx]
        rw [div_lt_iff₀ zero_lt_two, sub_lt_iff_lt_add]
        suffices 0 < √d by linarith
        rw [sqrt_pos]
        exact lt_of_le_of_ne hd0 (Ne.symm hd')
    -- r(k, y) < k + 1 iff y < k + 1.
    _ = {x : ℝ | y < k + 1 ∧ x = r k y} := by
        ext x
        simp only [← and_assoc, Set.mem_setOf_eq, and_congr_left_iff]
        intro hx
        subst x
        simp [le_of_lt (hr1 hy), hr2 (le_of_lt hy)]
    _ = if k + 1 ≤ y then (∅ : Set ℝ) else {(k + √(k^2 + 4 * y)) / 2} := by ext x; simp
  -- Define b(y) = ⌈y⌉₊ if {y} ≠ 0 and b(y) = ⌈y⌉₊ + 1 if {y} = 0.
  set b : ℝ → ℕ := fun y => Nat.ceil y + if Int.fract y = 0 then 1 else 0
  -- Assume that 0 ≤ y and show that b(y) is the smallest natural number n such that n > y.
  have hb {k : ℕ} {y : ℝ} (hy : 0 ≤ y) : y < k ↔ b y ≤ k := by
    simp_rw [b, Int.fract]
    split_ifs with hy1
    · rw [show y = ⌊y⌋ by linarith]
      norm_cast
      have hy0 : 0 ≤ ⌊y⌋ := by rwa [Int.floor_nonneg]
      simp only [Nat.ceil_intCast]
      omega
    simp
    rw [lt_iff_le_and_ne]
    suffices y ≠ k by tauto
    contrapose! hy1
    simp [hy1]
  -- If 1 < y < k + 1 then b(r(k, y) - 1) = k.
  have hbr {k : ℕ} {y : ℝ} (hy : 1 < y) (hyk : y < k + 1) : b (r k y - 1) = k := by
    have hk1 : 1 ≤ k := by
      suffices 0 < k by omega
      rify
      linarith
    rify at hk1
    -- We have k < r(k, y) (since 0 < y).
    replace hr1 := @hr1 k y (by linarith)
    -- We have r(k, y) < k + 1.
    replace hr2 := (@hr2 k y (by linarith)).mpr hyk
    -- k < r(k, y) < k + 1 implies that the fractional part of r(k, y) is non-zero.
    have h : Int.fract (r k y) ≠ 0 := by
      apply ne_of_gt
      rw [Int.fract_pos]
      suffices ⌊r k y⌋ = k by
        simp [this]
        linarith
      rw [Int.floor_eq_iff]
      simp [hr2, le_of_lt hr1]
    -- We get that b(r(k, y) - 1) = ⌈r(k, y)⌉ - 1.
    simp [b, h]
    zify
    rw [Int.natCast_ceil_eq_ceil (by linarith), Int.ceil_sub_one]
    -- The result follows from ⌈r(k, y)⌉ = k + 1.
    suffices ⌈r k y⌉ = k + 1 by linarith
    rw [Int.ceil_eq_iff]
    simp [hr1, le_of_lt hr2]
  -- Assume that 1 ≤ y < n + 1 and assume that 0 ≤ g(x) ≤ x for all 0 ≤ x.
  -- Show that the number of solutions of the equation f(g(x)) = y for x ∈ [0, n) is equal
  -- to the following sum:
  -- ∑ k ∈ [b(y - 1), n), (number of solutions of g(x) = r(k, y) for x ∈ [0, n)).
  have hsol {n : ℕ} {y : ℝ} {g : ℝ → ℝ} (hn : 0 < n) (hy1 : 1 ≤ y) (hyn : y < n + 1)
        (hg_nonneg : ∀ x, 0 ≤ x → 0 ≤ g x)
        (hg : ∀ x, 0 ≤ x → g x ≤ x) :
        {x : ℝ | 0 ≤ x ∧ x < n ∧ f (g x) = y}.encard =
          ∑ k ∈ Finset.Ico (b (y - 1)) n, {x : ℝ | 0 ≤ x ∧ x < n ∧ g x = r k y}.encard := calc
    -- {x : ℝ | 0 ≤ x ∧ x < n ∧ f (g x) = y}
    --    = ⋃ k ∈ [0, n), {x : ℝ | 0 ≤ x ∧ x < n ∧ k ≤ g x ∧ g x < k + 1 ∧ f (g x) = y}).
    -- In other words, split the range of g(x) into intervals [k, k + 1) for k ∈ [0, n) and
    -- take the union of solutions of f(g(x)) = y on these intervals.
    {x : ℝ | 0 ≤ x ∧ x < n ∧ f (g x) = y}.encard = (⋃ k ∈ Finset.range n, {x : ℝ | 0 ≤ x ∧ x < n ∧ k ≤ g x ∧ g x < k + 1 ∧ f (g x) = y}).encard := by
        congr; ext x; simp
        intro hx1 hx2
        refine ⟨?_, by tauto⟩
        intro h
        simp only [h, and_true]
        -- We need to show that 0 ≤ x < n, f(g(x)) = y implies that there exists
        -- k < n such that k ≤ g(x) < k + 1.
        -- Take k = |⌊g(x)⌋|.
        use ⌊g x⌋.natAbs
        -- |⌊g(x)⌋| = ⌊g(x)⌋ because 0 ≤ g(x) for 0 ≤ x.
        have eq : ⌊g x⌋.natAbs = ⌊g x⌋ := by
          rw [Int.natAbs_of_nonneg]
          rw [Int.floor_nonneg]
          exact hg_nonneg x hx1
        rw [show (⌊g x⌋.natAbs : ℝ) = (⌊g x⌋.natAbs : ℤ) from rfl, eq]
        rw [← and_assoc, ← Int.floor_eq_iff]
        simp only [true_and]
        zify [hn]
        simp only [Int.natCast_natAbs] at eq
        rw [eq]
        -- It is left to show that ⌊g(x)⌋ < n.
        suffices ⌊g x⌋ < n by omega
        simp only [Int.floor_lt, Int.cast_natCast]
        -- We have ⌊g(x)⌋ ≤ g(x) ≤ x < n.
        apply lt_of_le_of_lt _ hx2
        exact hg x hx1
    -- Show that the cardinality of a finite union of sets is the sum of cardinalities of these sets.
    _ = ∑ k ∈ Finset.range n, {x : ℝ | 0 ≤ x ∧ x < n ∧ k ≤ g x ∧ g x < k + 1 ∧ f (g x) = y}.encard := by
        clear * -
        generalize Finset.range n = s
        -- Proof by induction on a finite set s.
        induction s using Finset.induction with
        | empty => simp
        | @insert x r hxr ih =>
          simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
          rw [Set.encard_union_eq, ih, Finset.sum_insert hxr]
          -- We need to show that all sets are disjoint.
          -- Sets are disjoint because k ≤ g(x) < k + 1 and i ≤ g(x) < i + 1 imply
          -- that k = i.
          simp only [Set.disjoint_iUnion_right]
          intro k hk
          rw [Set.disjoint_iff]
          intro i
          simp
          intro hi1 hi2 hxgi hgix eq _ _ hkgi hgik
          contrapose! hxr
          suffices x = k by rwa [this]
          apply eq_of_le_of_le
          · suffices x < k + 1 by omega
            rify
            linarith
          · suffices k < x + 1 by omega
            rify
            linarith
    -- f(g(x)) = y for x ∈ [0, n), g(x) ∈ [k, k + 1) is equivalent to
    -- g(x) = r(k, y) and y < k + 1 for x ∈ [0, n).
    -- This result follows directly from hsol1.
    _ = ∑ k ∈ Finset.range n, {x : ℝ | 0 ≤ x ∧ x < n ∧ g x = r k y ∧ y < k + 1}.encard := by
        apply Finset.sum_congr rfl
        intro k hk
        congr; ext x; simp
        intro hx1 hx2
        have := hsol1 k y (by linarith)
        apply_fun (g x ∈ ·) at this
        simp at this
        rw [this, and_comm]
    -- ∑ k ∈ [0, n), {x | x ∈ [0, n) ∧ g(x) = r(k, y) ∧ y < k + 1}
    --   = ∑ k ∈ [b(y - 1), n), {x | x ∈ [0, n), g(x) = r(k, y)}.
    _ = 0 + ∑ k ∈ Finset.Ico (b (y - 1)) n, {x : ℝ | 0 ≤ x ∧ x < n ∧ g x = r k y}.encard := by
        -- We have b(y - 1) ≤ n.
        have : b (y - 1) ≤ n := by
          rw [← hb (by linarith)]
          linarith
        -- We know that b(y - 1) ≤ k iff y - 1 < k (or y < k + 1).
        -- So y ≥ k + 1 is equivalent to b(y - 1) > k and ∑ k ∈ [0, b(y - 1)), _ = 0.
        rw [← Finset.sum_range_add_sum_Ico _ this]
        congr 1
        · apply Finset.sum_eq_zero
          simp only [Finset.mem_range, Set.encard_eq_zero]
          intro k hk
          ext x; simp; intros
          suffices k ≤ y - 1 by linarith
          contrapose! hk
          rwa [hb (by linarith)] at hk
        · apply Finset.sum_congr rfl
          simp only [Finset.mem_Ico, and_imp]
          intro k hk1 hk2
          rw [← hb (by linarith)] at hk1
          congr; ext x; simp; intros
          linarith
    _ = ∑ k ∈ Finset.Ico (b (y - 1)) n, {x : ℝ | 0 ≤ x ∧ x < n ∧ g x = r k y}.encard := by rw [zero_add]
  -- Calculate the number of solutions of f(f(f(x))) = 17 for x ∈ [0, 2020].
  calc
    -- f(f(f(x))) = 17 has no solutions for x = 2020 because f(f(f(2020)))) = 0.
    -- So we can replace the requirement x ∈ [0, 2020] with x ∈ [0, 2020).
    {x | 0 ≤ x ∧ x ≤ 2020 ∧ f (f (f x)) = 17}.encard = {x : ℝ | 0 ≤ x ∧ x < (2020 : ℕ) ∧ f (f (f x)) = 17}.encard := by
        congr; ext x; simp
        intro hx hf3
        rw [le_iff_eq_or_lt]
        suffices x ≠ 2020 by tauto
        contrapose! hf3
        simp [hf3, hf]
    -- Apply the lemma hsol to f(f(f(x))) = 17 with g(x) = f(f(x)) and get
    -- number of solutions = ∑ i ∈ [17, 2020), #{x | x ∈ [0, 2020) ∧ f(f(x)) = r(i, 17)}
    -- (here # denotes the cardinality of the set of solutions).
    _ = ∑ i ∈ Finset.Ico (17 : ℕ) 2020, {x : ℝ | 0 ≤ x ∧ x < (2020 : ℕ) ∧ f (f x) = r i 17}.encard := by
        -- We have b(17 - 1) = 17.
        have hb16 : b (17 - 1) = 17 := by norm_num [b]
        rw [hsol (y := 17) (by norm_num) (by norm_num) (by norm_num), hb16]
        -- We only need to show that 0 ≤ f(f(x)) ≤ x for 0 ≤ x.
        -- These results follow from 0 ≤ f(x) ≤ x for 0 ≤ x.
        · intro x hx
          apply hf_nonneg
          apply hf_nonneg x hx
        · intro x hx
          trans f x
          · apply hf_le
            apply hf_nonneg x hx
          · apply hf_le x hx
    -- Apply hsol to #{x | x ∈ [0, 2020) ∧ f(f(x)) = r(i, 17)} with g(x) = f(x) and get
    -- #{x | x ∈ [0, 2020) ∧ f(f(x)) = r(i, 17)} = ∑ j ∈ [i, 2020), #{x | x ∈ [0, 2020) ∧ f(x) = r(j, r(i, 17))}.
    _ = ∑ i ∈ Finset.Ico (17 : ℕ) 2020, ∑ j ∈ Finset.Ico i 2020, {x : ℝ | 0 ≤ x ∧ x < (2020 : ℕ) ∧ f x = r j (r i 17)}.encard := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_Ico] at hi
        rify at hi
        -- We have i < r(i, 17) < i + 1.
        replace hr1 := @hr1 i 17 (by norm_num)
        replace hr2 := (@hr2 i 17 (by norm_num)).mpr (by linarith)
        -- We have b(r(i, 17) - 1) = i.
        replace hbr : b (r i 17 - 1) = i := by rw [hbr (by norm_num) (by linarith)]
        rw [hsol (by norm_num) (by linarith) (by norm_num; linarith) hf_nonneg hf_le, hbr]
    -- Apply hsol to #{x | x ∈ [0, 2020) ∧ f(x) = r(j, r(i, 17))} with g(x) = x and get
    -- #{x | x ∈ [0, 2020) ∧ f(x) = r(j, r(i, 17))} = ∑ k ∈ [j, 2020), 1.
    _ = ∑ i ∈ Finset.Ico (17 : ℕ) 2020, ∑ j ∈ Finset.Ico i 2020, ∑ k ∈ Finset.Ico j 2020, (1 : WithTop ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_Ico] at hi hj
        rify at hi hj
        -- We have i < r(i, 17) < i + 1.
        have hri1 := @hr1 i 17 (by norm_num)
        have hri2 := (@hr2 i 17 (by norm_num)).mpr (by linarith)
        -- We have i ≤ j < r(j, r(i, 17)) < j + 1.
        have hrj1 := @hr1 j (r i 17) (by linarith)
        have hrj2 := (@hr2 j (r i 17) (by linarith)).mpr (by linarith)
        -- We have b(r(j, r(i, 17)) - 1) = j.
        replace hbr : b (r j (r i 17) - 1) = j := by rw [hbr (by linarith) (by linarith)]
        -- After applying hsol with g(x) = x we get
        -- #{x | x ∈ [0, 2020) ∧ f(x) = r(j, r(i, 17))} = ∑ k ∈ [j, 2020), #{x | x ∈ [0, 2020) ∧ x = r(k, r(j, r(i, 17)))}.
        rw [hsol (by norm_num) (by linarith) (by norm_num; linarith) (by simp) (by simp), hbr]
        -- It is left to show that #{x | x ∈ [0, 2020) ∧ x = r(k, r(j, r(i, 17)))} = 1 for
        -- 17 ≤ i ≤ j ≤ k < 2020.
        apply Finset.sum_congr rfl
        intro k hk
        rw [Set.encard_eq_one]
        -- We need to show that r(k, r(j, r(i, 17))) ∈ [0, 2020).
        use r k (r j (r i 17))
        ext x
        simp [← and_assoc]
        intro hx
        subst x
        simp only [Finset.mem_Ico] at hk
        have hk2 : k + 1 ≤ 2020 := by omega
        rify at hk hk2
        -- We have k < r(k, r(j, r(i, 17))) < k + 1 so r(k, r(j, r(i, 17))) ∈ [0, 2020).
        have hrk1 := @hr1 k (r j (r i 17)) (by linarith)
        have hrk2 := (@hr2 k (r j (r i 17)) (by linarith)).mpr (by linarith)
        constructor <;> linarith
    -- Show that ∑ i ∈ [17, 2020), ∑ j ∈ [i, 2020), ∑ k ∈ [j, 2020), 1 = Nat.choose 2005 3.
    _ = Nat.choose 2005 3 := by
        clear * -
        rw [show 2020 = 2002 + 18 by norm_num, show 2005 = 2002 + 3 by norm_num]
        generalize 2002 = n
        norm_cast
        -- Prove a general result:
        -- ∑ i ∈ [17, n + 18), ∑ j ∈ [i, n + 18), ∑ k ∈ [j, n + 18), 1 = Nat.choose (n + 3) 3.
        -- We have the following identity:
        -- Nat.choose (n + 1) (k + 1) = ∑ m ∈ [0, n - k + 1), Nat.choose (n - m) k.
        have h {n k} (hnk : k ≤ n) : Nat.choose (n + 1) (k + 1) = ∑ m ∈ Finset.range (n - k + 1), Nat.choose (n - m) k := by
          rw [show n + 1 = (n - k) + k + 1 by omega]
          rw [← Nat.sum_range_add_choose, ← Finset.sum_flip]
          apply Finset.sum_congr rfl
          intro m hm
          simp only [Finset.mem_range] at hm
          congr
          omega
        -- We get Nat.choose (n + 3) 3 = ∑ i ∈ [0, n + 1), Nat.choose (n + 2 - i) 2.
        rw [h (by omega)]
        -- We have ∑ i ∈ [17, n + 18), h(i) = ∑ i ∈ [0, n + 1), h(i + 17).
        rw [Finset.sum_Ico_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Nat.reduceSubDiff, Finset.mem_range] at hi
        rw [show n + 2 - i = n - i + 2 by omega]
        -- We need to show that h(i + 17) = ∑ j ∈ [i + 17, n + 18), ∑ k ∈ [j, n + 18), 1 = Nat.choose (n - i + 2) 2
        -- for i < n + 1.
        -- We have Nat.choose (n - i + 2) 2 = ∑ j ∈ [0, n - i + 1), Nat.choose (n - i - j + 1) 1.
        rw [h (by omega)]
        -- We also have ∑ j ∈ [i + 17, n + 18), h₁(j) = ∑ j ∈ [0, n - i + 1), h₁(j + i + 17).
        rw [Finset.sum_Ico_eq_sum_range]
        rw [show n - i + 1 - 1 + 1 = n - i + 1 by omega, show n + 18 - (17 + i) = n - i + 1 by omega]
        -- It is left to show that h₁(j + i + 17) = ∑ k ∈ [j + i + 17, n + 18), 1 = Nat.choose (n - i - j + 1) 1.
        apply Finset.sum_congr rfl
        intro j hj
        -- We get h₁(j + i + 17) = n + 18 - j - i - 17 = n - i - j + 1 and
        -- Nat.choose (n - i - j + 1) 1 = n - i - j + 1 = h₁(j + i + 17).
        simp
        omega