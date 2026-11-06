import Mathlib

open Finset Fin OrderDual

/-- Find all integers $n \geqslant 3$ with the following property: for all real numbers $a_{1}, a_{2}, \ldots, a_{n}$ and $b_{1}, b_{2}, \ldots, b_{n}$ satisfying $\left|a_{k}\right|+\left|b_{k}\right|=1$ for $1 \leqslant k \leqslant n$, there exist $x_{1}, x_{2}, \ldots, x_{n}$, each of which is either -1 or 1 , such that
\[ \left|\sum_{k=1}^{n} x_{k} a_{k}\right|+\left|\sum_{k=1}^{n} x_{k} b_{k}\right| \leqslant 1 \] -/
theorem algebra_24735 :
    {n : ℕ | n ≥ 3 ∧
      ∀ a b : Fin n → ℝ, (∀ k, |a k| + |b k| = 1) →
      ∃ x : Fin n → ℝ, (∀ k, |x k| = 1) ∧ |∑ k, x k * a k| + |∑ k, x k * b k| ≤ 1} =
    {n : ℕ | n ≥ 3 ∧ Odd n} := by
  ext n
  simp only [ge_iff_le, Set.mem_setOf_eq, and_congr_right_iff]
  intro hn
  -- Resolve the goal `p ↔ q` to two goals `q → p` and `¬q → ¬p`.
  apply fun p q => show (q → p) → (¬q → ¬p) → (p ↔ q) by tauto
  · intro odd a b eq
    -- For any odd integer $n \geqslant 3$, we may assume without loss of generality $b_{k} \geqslant 0$ for $1 \leqslant k \leqslant n$
    wlog b_nonneg : ∀ k, 0 ≤ b k generalizing a b
    · -- The sign function; note that here `sign 0 = 1` instead of `sign 0 = 0`, this is required to ensure that `|sign x| = 1`.
      let sign : ℝ → ℝ := fun x => if 0 ≤ x then 1 else -1
      have abs_sign (x : ℝ) : |sign x| = 1 := by simp only [sign]; split_ifs <;> simp
      have abs_eq_sign_mul (x : ℝ) : |x| = sign x * x := by
        simp only [sign]
        split_ifs with h <;> simp [h]
        linarith
      -- this can be done by flipping the pair $\left(a_{k}, b_{k}\right)$ to $\left(-a_{k},-b_{k}\right)$ and $x_{k}$ to $-x_{k}$ if necessary
      specialize this (fun k => sign (b k) * a k) (fun k => sign (b k) * b k)
        (by simpa [abs_mul, abs_sign]) (by simp [← abs_eq_sign_mul])
      simp only [← mul_assoc] at this
      obtain ⟨x, hx⟩ := this
      use (fun k => x k * sign (b k))
      simpa only [abs_mul, abs_sign, mul_one]
    -- we may assume without loss of generality $a_{1} \geqslant a_{2} \geqslant \cdots \geqslant a_{m} \geqslant 0>a_{m+1} \geqslant \cdots \geqslant a_{n}$
    wlog sorted : Antitone a generalizing a b
    · -- Using `OrderDual` to convert antitonicity to monotonicity, so we can use the lemma `Tuple.monotone_sort`.
      let f := Tuple.sort (toDual ∘ a)
      specialize this (a ∘ f) (b ∘ f)
        (by simpa using fun k => eq (f k))
        (by simpa using fun k => b_nonneg (f k))
        (by simpa [← monotone_toDual_comp_iff, f] using Tuple.monotone_sort _)
      obtain ⟨x, hx₁, hx₂⟩ := this
      refine ⟨fun k => x (f⁻¹ k), ?_, ?_⟩
      · simpa using fun _ => hx₁ _
      · have := fun c : Fin n → ℝ =>
          Equiv.Perm.sum_comp f ⊤ (f := fun k => x (f⁻¹ k) * c k) (by simp)
        simp only [top_eq_univ, Equiv.Perm.inv_apply_self] at this
        simpa only [Function.comp_apply, this] using hx₂
    -- We claim that the choice $x_{k}=(-1)^{k+1}$ for $1 \leqslant k \leqslant n$ will work.
    refine ⟨fun k => (-1) ^ (k : ℕ), by simp, ?_⟩
    dsimp only
    let m := (List.ofFn a).findIdx (· < 0)
    let S := univ.filter (fun x : Fin n => x < m)
    let T := univ.filter (fun x : Fin n => m ≤ x)
    -- Define  $$ s=\sum_{k=1}^{m} x_{k} a_{k} \quad \text { and } \quad t=-\sum_{k=m+1}^{n} x_{k} a_{k} . $$
    let s := ∑ k ∈ S, (-1) ^ (k : ℕ) * a k
    let t := -∑ k ∈ T, (-1) ^ (k : ℕ) * a k
    -- `a k ≥ 0` when `k < m`
    have a_S_nonneg {k} (hk : k ∈ S) : 0 ≤ a k := by
      simp only [mem_filter, mem_univ, true_and, S] at hk
      simpa using List.not_of_lt_findIdx hk
    -- `a k < 0 `when `k ≥ m`
    have a_T_neg {k} (hk : k ∈ T) : a k < 0 := by
      simp only [mem_filter, mem_univ, true_and, T] at hk
      -- `a m < 0`, and by the antitonicity of `a`, we have `a k < 0` since `k ≥ m`.
      have := List.findIdx_get
        (w := show m < (List.ofFn a).length from lt_of_le_of_lt hk (by simp))
      simp only [List.get_eq_getElem, List.getElem_ofFn, decide_eq_true_eq] at this
      change a ⟨m, _⟩ < 0 at this
      refine lt_of_le_of_lt ?_ this
      apply sorted
      rwa [le_iff_val_le_val]
    -- It is sufficient to prove that `s ∈ [0, 1]` and `t ∈ [0, 1]`.
    suffices s ∈ Set.Icc 0 1 ∧ t ∈ Set.Icc 0 1 by
      -- To split the sum, we need the fact that `S` and `T` are disjoint and the union of
      -- them is the universal set.
      have S_union_T : S ∪ T = univ := by
        ext k; simp [S, T]; omega
      have S_disj_T : Disjoint S T := by
        rw [disjoint_iff_inter_eq_empty]; ext k; simp [S, T]
      have b_eq (k) : b k = 1 - |a k| := by
        specialize eq k
        rw [abs_of_nonneg (b_nonneg k)] at eq
        linarith
      suffices |s - t| + |1 - s - t| ≤ 1 by
        -- It follows that $\sum_{k=1}^{n} x_{k} a_{k}=s-t$ and $\sum_{k=1}^{n} x_{k} b_{k}=1-s-t$.
        rw [← Nat.not_even_iff_odd] at odd
        simp [b_eq, mul_sub, ← sum_range, neg_one_geom_sum, odd]
        simp [s, t] at this
        simpa (config := {contextual := true})
          [← S_union_T, sum_union S_disj_T, abs_of_nonneg, a_S_nonneg,
          abs_of_neg, a_T_neg, ← sub_sub]
      -- Hence it remains to prove  $$ |s-t|+|1-s-t| \leqslant 1 $$  under the constraint $0 \leqslant s, t \leqslant 1$.
      clear_value s t
      -- By symmetry, we may assume $s \geqslant t$.
      wlog ge : s - t ≥ 0 generalizing s t with h
      · simp at ge
        specialize h s t ⟨this.2, this.1⟩ (by linarith)
        convert h using 2
        · apply abs_sub_comm
        · ring_nf
      · simp only [Set.mem_Icc] at this
        by_cases ge' : 1 - s - t ≥ 0
        · -- If $1-s-t \geqslant 0$, then we have  $$ |s-t|+|1-s-t|=s-t+1-s-t=1-2 t \leqslant 1 $$
          rw [abs_of_nonneg ge, abs_of_nonneg ge']
          linarith
        · -- If $1-s-t \leqslant 0$, then we have  $$ |s-t|+|1-s-t|=s-t-1+s+t=2 s-1 \leqslant 1 $$
          simp only [ge_iff_le, not_le] at ge'
          rw [abs_of_nonneg ge, abs_of_neg ge']
          linarith
        -- Hence, the inequality is true in both cases. These show $n$ can be any odd integer greater than or equal to 3.
    -- We only need to prove that the alternating sum of `x` is in the range `[0, 1]`
    -- for a general class of tuples `x`.
    suffices ∀ m (x : Fin m → ℝ) (hx : ∀ k, x k ∈ Set.Icc 0 1) (sorted : Antitone x),
        ∑ k : Fin m, (-1) ^ (k : ℕ) * x k ∈ Set.Icc 0 1 by
      have a_range (k) : -1 ≤ a k ∧ a k ≤ 1 := by
        specialize eq k
        rw [← abs_le]
        have := abs_nonneg (b k)
        linarith
      -- Prove that `a k ∈ [0, 1]` for `k ∈ S`.
      have a_S_in_01 {k} (hk : k ∈ S) : a k ∈ Set.Icc 0 1 := by
        simpa using ⟨a_S_nonneg hk, (a_range k).2⟩
      -- Prove that `-a k ∈ [0, 1]` for `k ∈ T`.
      have neg_a_T_in_01 {k} (hk : k ∈ T) : -a k ∈ Set.Icc 0 1 := by
        specialize a_range k
        specialize a_T_neg hk
        simpa using ⟨by linarith, by linarith⟩
      constructor
      · -- Convert the value of `s` to the alternating sum of sequence `a k` for `k < m`.
        have m_le_n : m ≤ (List.ofFn a).length := by apply List.findIdx_le_length
        simp only [List.length_ofFn] at m_le_n
        -- Firstly, we rewrite the summation range `S` to the image of `castLE`.
        have S_eq : S = univ.image (castLE m_le_n) := by
          ext k
          simp only [S, mem_image_univ_iff_mem_range, range_castLE]
          simp
        simp only [s]
        rw [S_eq, sum_image (by simp)]
        simp only [coe_castLE]
        refine this m (fun k => a (k.castLE m_le_n)) ?_ ?_
        -- Prove that the sequence `k ↦ a k` satisfies the condition in our given assumption,
        -- which means `a` is decreasing and every element in `a` is in the interval `[0, 1]`.
        · intro k
          apply a_S_in_01
          simp [S]
        · intro i j le
          apply sorted
          rw [le_iff_val_le_val]
          simpa
      · -- Convert the value of `t` to the alternating sum of sequence `-a (n - 1 - k)`
        -- for `k < n - m`. So it is also in the range `[0, 1]`.
        have lt_imply : ∀ k < n - m, n - 1 - k < n := by omega
        let f (k : Fin (n - m)) : Fin n := ⟨n - 1 - k, lt_imply _ k.2⟩
        -- `T` is the range of `f`.
        have T_eq : T = univ.image f := by
          ext k
          simp only [mem_filter, mem_univ, true_and, mem_image, Fin.ext_iff, T, f]
          refine ⟨fun h => ⟨⟨n - 1 - k, ?_⟩, ?_⟩, fun ⟨x, hx⟩ => ?_⟩
          · omega
          · dsimp only; omega
          · omega
        simp only [t]
        -- Rewriting the sum using `sum_image`.
        rw [T_eq, sum_image (by simp [f, val_eq_val]; omega)]
        -- Use `conv` and `enter` to rewrite `(-1) ^ (f x)` to `(-1) ^ x`.
        conv =>
          simp only [← sum_neg_distrib, ← mul_neg]
          enter [2, 2, x]
          rw [neg_one_pow_eq_pow_mod_two,
            show (n - 1 - x) % 2 = x % 2 by cases' odd; omega,
            ← neg_one_pow_eq_pow_mod_two]
        -- Now we can use the introduced hypothesis `this` to finish the proof.
        refine this (n - m) (fun k => -a (f k)) ?_ ?_
        · -- We need to check the conditions are satisfied: firstly, every `-a (f k)` are in
          -- the range `[0, 1]`.
          intro k
          apply neg_a_T_in_01
          simp [f, T]
          omega
        · -- We need to prove the sequence `-a (f k)` is antitone. This can be proved
          -- from the fact that both `a`, `f` is antitone, and the function `x ↦ -x` is antitone.
          intro i j le
          simp only [neg_le_neg_iff, f]
          apply sorted
          simp only [le_iff_val_le_val, tsub_le_iff_right] at le ⊢
          omega
    -- Remove all hypotheses, since they wouldn't be used later.
    clear * -
    -- It is sufficient to prove the theorem for lists, rather than tuples (`Fin m → ℝ`).
    suffices ∀ (x : List ℝ) (hx : x.Forall (· ∈ Set.Icc 0 1)) (sorted : x.Sorted (· ≥ ·)),
        x.alternatingSum ∈ Set.Icc 0 1 by
      intro m x hx sorted
      specialize this (List.ofFn x)
      -- Simplifying `List.Forall`, `List.Sorted` with `List.ofFn`.
      simp only [List.forall_iff_forall_mem, List.forall_mem_ofFn_iff, ge_iff_le,
        List.sorted_ofFn_iff, List.alternatingSum_eq_finset_sum, Int.reduceNeg,
        getElem_fin, List.getElem_ofFn, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
        Int.cast_one] at this
      -- We can't simplify `(List.ofFn x).length` to `m` here, so we have to use `convert`.
      have m_eq : m = (List.ofFn x).length := by simp
      convert this hx (fun i j lt => sorted (le_of_lt lt))
    -- Now use a recursion to prove that, if `x` is non-empty, decreasing and every
    -- element are in the range `[0, 1]`, the alternating sum of `x` is in the range `[0, x₀]`.
    let rec f (x : List ℝ)
        (ne : x ≠ []) (hx : x.Forall (· ∈ Set.Icc 0 1)) (sorted : x.Sorted (· ≥ ·)) :
        0 ≤ x.alternatingSum ∧ x.alternatingSum ≤ x.head ne :=
      -- Split into four cases: `x` has length 0, 1, 2, ≥ 3. we need `x ≥ 3` in the last case
      -- because we have used the fact that `c :: x` is non-empty list.
      match x with
      | [] => by simp at ne
      | [a] => by simpa using hx.1
      | [a, b] => by
        simp at hx sorted ⊢
        exact ⟨sorted, hx.2.1⟩
      | a :: b :: c :: x => by
        simp only [List.Forall] at hx
        rw [List.sorted_cons, List.sorted_cons] at sorted
        simp only [List.mem_cons, ge_iff_le, forall_eq_or_imp] at sorted
        have := f (c :: x) (by simp) hx.2.2 sorted.2.2
        simp at this ⊢
        -- `linarith` can't deal with the goal of type `p ∧ q`, so we have to split it.
        exact ⟨by linarith, by linarith⟩
    intro x hx sorted
    -- Split out the empty case.
    by_cases ne : x = []
    · simp [ne]
    · -- For the non-empty case, the alternating sum is in the range `[0, x₀]`, and
      -- `x₀ ≤ 1` because every element in the list `x` is less or equal than 1, so it is in the
      -- range `[0, 1]`.
      have := f x ne hx sorted
      simp only [Set.mem_Icc]
      refine ⟨this.1, this.2.trans ?_⟩
      simp only [List.forall_iff_forall_mem, Set.mem_Icc] at hx
      specialize hx (x.head ne) (by simp)
      linarith
  · -- For any even integer $n \geqslant 4$
    simp only [Nat.not_odd_iff_even, not_forall, Classical.not_imp, not_exists,
      not_and, not_le]
    intro ev
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    rw [hm]
    -- we consider the case  $$ a_{1}=a_{2}=\cdots=a_{n-1}=b_{n}=0 \quad \text { and } \quad b_{1}=b_{2}=\cdots=b_{n-1}=a_{n}=1 $$
    use fun k => if k = last m then 1 else 0,
      fun k => if k ≠ last m then 1 else 0
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
      ↓reduceIte, ne_eq, ite_not, exists_prop]
    constructor
    · -- The condition $\left|a_{k}\right|+\left|b_{k}\right|=1$ is satisfied for each $1 \leqslant k \leqslant n$.
      intro k
      split_ifs <;> simp
    · -- This part proves that $\left|\sum_{k=1}^{n} x_{k} a_{k}\right| \geqslant 1$ and $\left|\sum_{k=1}^{n} x_{k} b_{k}\right| \geqslant 1$, which shows (1) cannot hold.
      intro x' hx'
      simp only [← Int.cast_abs, hx', Int.cast_one, lt_add_iff_pos_right, abs_pos, ne_eq]
      -- The first sum `|∑ k, x k * a k|` is equal to 1, so we only need to
      -- prove that `|∑ k, x k * b k|` ≠ 0.
      intro h
      -- Convert the goal to integer case.
      have x'_int : ∀ k, ∃ x : ℤ, x' k = x := by
        intro k
        specialize hx' k
        rw [show (1 : ℝ) = |1| by simp, abs_eq_abs] at hx'
        cases hx' with
        | inl hx' => simpa [hx'] using ⟨1, by simp⟩
        | inr hx' => simpa [hx'] using ⟨-1, by simp⟩
      choose x x'_eq using x'_int
      simp only [x'_eq] at h hx'
      norm_cast at h hx'
      rename' hx' => hx
      clear x' x'_eq
      -- Now we converted `x` to `Fin (m + 1) → ℤ`, so we can lift it to `ZMod 2`.
      replace hx k : (x k : ZMod 2) = 1 := by
        specialize hx k
        simp only [← Int.isUnit_iff_abs_eq, Int.isUnit_iff] at hx
        cases' hx with hx hx <;> simp [hx]
        simpa using show ((-1 : ZMod 2) = 1 : Bool) = true from rfl
      -- No matter how we choose each $x_{k}$, both sums $\sum_{k=1}^{n} x_{k} a_{k}$ and $\sum_{k=1}^{n} x_{k} b_{k}$ are odd integers.
      simp only [sum_ite, sum_const_zero, zero_add] at h
      apply_fun ((↑) : Int → ZMod 2) at h
      simp only [Int.cast_sum, hx, Finset.sum_const, nsmul_eq_mul, mul_one, Int.cast_zero,
        show univ.filter (· ≠ last m) = univ \ {last m} by ext; simp] at h
      -- We can convert the sum to the cardinal of finite set `{0, ..., m - 1}`, because
      -- every summand is equal to `1` modulo `2`.
      rw [card_sdiff (by simp)] at h
      rw [← ZMod.eq_zero_iff_even] at ev
      simp only [card_univ, Fintype.card_fin, card_singleton, add_tsub_cancel_right] at h
      -- Now `m ≡ 0 (mod 2)`, this is impossible, beacuse `n` is even and `m = n - 1`.
      apply_fun ((↑) : Nat → ZMod 2) at hm
      simp [ev, h] at hm
