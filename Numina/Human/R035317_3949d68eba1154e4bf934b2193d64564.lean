import Mathlib

/-- A set $\mathcal S$ of distinct positive integers has the following property:
    for every integer x in $\mathcal S$, the arithmetic mean of the set of values obtained by deleting
    x from $\mathcal S$ is an integer.  Given that 1 belongs to $\mathcal S$ and that 2002 is the
    largest element of $\mathcal S$, what is the greatest number of elements that $\mathcal S$ can have? -/
theorem number_theory_97806 (S : Finset ℕ) (hS : ∀ x ∈ S, (S \ {x}).card > 0)
    (hS1 : ∀ x ∈ S, ∃ k : ℕ, (S \ {x}).sum id = k * (S \ {x}).card) (hS2 : 1 ∈ S)
    (hS3 : S.max = 2002) (hS4 : ∀ x ∈ S, x > 0):
    S.card ≤ 30 := by
  -- Let the sum of integers in S be N
  let N := S.sum id
  have hne : S.Nonempty := ⟨1, hS2⟩
  -- and let the size of S be n + 1.
  obtain ⟨n, eq⟩ : ∃ n, S.card = n + 1 := Nat.exists_eq_add_one.mpr hne.card_pos
  have eq_erased (x) : S \ {x} = S.erase x := by
    ext a; simp[And.comm]
  -- after any element x is removed
  -- the cardinality is lowered to n
  have card_removed : ∀ x ∈ S, (S \ {x}).card = n := by
    intro x hx
    rw[eq_erased, Finset.card_erase_of_mem hx, eq, Nat.add_sub_cancel]
  -- and the sum is lowered to N - x
  have sum_removed : ∀ x ∈ S, (S \ {x}).sum id = N - x := by
    intro x hx
    unfold N
    rw[eq_erased, ← Finset.sum_erase_add (s := S) id hx]
    simp
  have elem_le_sum : ∀ x ∈ S, x ≤ N := by
    intro x hx
    change id x ≤ N
    apply Finset.single_le_sum _ hx
    intro _ _
    simp
  -- so $x \equiv N (\mod n)$
  have x_mod : ∀ x ∈ S, x ≡ N [MOD n] := by
    intro x hx
    obtain ⟨k,eq⟩ := hS1 x hx
    -- since $n | N - x$
    rw[card_removed x hx, sum_removed x hx] at eq
    have : N - x ≡ 0 [MOD n] := by
      rw[Nat.modEq_zero_iff_dvd]
      exists k
      rw[eq, mul_comm]
    have := Nat.ModEq.add_right x this
    simp at this
    symm
    rwa[Nat.sub_add_cancel (elem_le_sum x hx)] at this
  -- Since $1 \in S$, $N \equiv 1 (\mod n)$.
  have mod1 : 1 ≡ N [MOD n] := x_mod _ hS2
  -- Since the elements are positive integers, the largest element is at least n^2 + 1
  have largest_ge : S.max' hne ≥ n^2 + 1 := by
    have cardinality : (S ∩ Finset.Iio (n^2+1)).card ≤ n := by
    -- which is the (n+1)-th positive integer congruent to 1 mod n.
    -- We utilize cardinality facts about the image of sets under functions.
      have subs : ↑ S ∩ Finset.Iio (n^2+1) ⊆ Finset.image (fun m => m * n + 1) (Finset.Iio n) := by
        intro k
        simp only [Finset.mem_inter, Finset.mem_Iio, Finset.mem_image, and_imp]
        intro hk klt
        obtain ⟨a,eq⟩ := (Nat.modEq_iff_dvd' (hS4 _ hk)).mp $ mod1.trans (x_mod _ hk).symm
        exists a
        rw[mul_comm, ← eq, Nat.sub_one_add_one $ ne_of_gt $ hS4 _ hk]
        refine ⟨?p,rfl⟩
        apply lt_of_mul_lt_mul_of_nonneg_left _ (Nat.zero_le n)
        rw[← eq]
        apply Nat.lt_of_succ_lt_succ
        have : (k - Nat.succ 0).succ = k := by simp[Nat.sub_one_add_one $ ne_of_gt $ hS4 _ hk]
        rwa[this, ← pow_two]
      trans
      · apply Finset.card_le_card subs
      · trans
        · apply Finset.card_image_le
        · apply le_of_eq
          simp
    by_contra! h
    -- If the cardinality of S restricted to an interval would be same as S's, it would be contained in it
    have card_same : (S ∩ Finset.Iio (n^2+1)).card = S.card := by
      suffices seq : S = S ∩ Finset.Iio (n^2+1) by rw[← seq]
      ext a
      simp only [Finset.mem_inter, Finset.mem_Iio, iff_self_and]
      intro ha
      apply lt_of_le_of_lt (Finset.le_max' _ _ ha) h
    rw[card_same, eq] at cardinality
    apply (Nat.not_succ_le_self _ cardinality).elim
  -- 2002 is the maximal element of S, as has been assumed
  have max'_eq : S.max' hne = 2002 := by
    have : ↑ (S.max' hne) = S.max:= Finset.coe_max' hne
    rw[← this] at hS3
    exact_mod_cast hS3
  -- hence $n^2 + 1 \le 2002$
  rw[max'_eq] at largest_ge
  -- and $n | 2001$, such that $nk = 2001$ for a $k$
  obtain ⟨k, eq'⟩ := (Nat.modEq_iff_dvd' (by simp)).mp $
    Nat.ModEq.add_right_cancel' 1 $ max'_eq ▸ mod1.trans (x_mod _ (S.max'_mem hne)).symm
  -- from the inequation, it follows that $n \le 44$
  have n_le : n ≤ 44 := by
    by_contra! hn
    rw[Nat.lt_iff_add_one_le, ← sq_le_sq₀ (by simp) (by simp)] at hn
    linarith
  rw[Nat.sub_zero] at eq'
  -- but there are no divisors of 2001 between 30 and 44
  have : n ≤ 29 := by
    by_contra! lt_n
    have : n ∈ Finset.Ioc 29 44 := by simp[lt_n, n_le]
    have mod_lem : 2001 % n = 0 := by simp[eq']
    fin_cases this <;> (norm_num at mod_lem)
  rw[eq]
  -- so n + 1 must be less than or equal to 30
  exact Nat.succ_le_succ this