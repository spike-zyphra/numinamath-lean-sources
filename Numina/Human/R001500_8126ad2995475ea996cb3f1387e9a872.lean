import Mathlib

/-
Lemma.
Let $b_{0}, b_{1}, \ldots$ be an infinite sequence. Assume that for every nonnegative integer $m$ there exists a nonnegative integer $n \in[m+1, m+r]$ such that $b_{m}=b_{n}$. Then for every indices $k \leqslant \ell$ there exists an index $t \in[\ell, \ell+r-1]$ such that $b_{t}=b_{k}$.
-/
lemma rep_gap {r : ℕ} {b : ℕ → ℝ} (hr : 0 < r)  (h : ∀ m : ℕ, ∃ n : ℕ, n ∈ Finset.Icc (m + 1) (m + r) ∧ b m = b n) : ∀ k l : ℕ, k ≤ l → ∃ t : ℕ, t ∈ Finset.Icc l (l + r - 1) ∧ b t = b k := by
  intro k l hl
  -- We show this by an induction on l
  induction l, hl using Nat.le_induction
  -- The base case is trivial
  case base =>
    use k
    simp
    omega
  -- For the induction step, use the induction hypothesis, it gives us a number m close to l such that $b_m = b_k$.
  case succ l _ ih =>
    obtain ⟨m, hm⟩ := ih
    -- Distinguish two cases according to whether m = l
    by_cases hm' : m = l
      -- If m = l, then use the assumption.
    · obtain ⟨n, hn⟩ := h l
      use n
      constructor
      convert hn.1 using 2
      omega
      rw [← hn.2, ← hm']
      exact hm.2
      -- If m > l, then m is what we are looking for.
    · use m
      constructor
      · replace hm := hm.1
        simp at hm ⊢
        constructor
        repeat omega
      · exact hm.2

/-
Lemma (continued).
Moreover, there are at most $r$ distinct numbers among the terms of $\left(b_{i}\right)$.
-/
lemma range_finite {r : ℕ} {b : ℕ → ℝ} (hr : 0 < r)  (h : ∀ m : ℕ, ∃ n : ℕ, n ∈ Finset.Icc (m + 1) (m + r) ∧ b m = b n) : Set.Finite (Set.range b) := by
  -- To prove the second claim, assume, to the contrary, that there exist $r+1$ distinct numbers $b_{i_{1}}, \ldots, b_{i_{r+1}}$.
  rw [← Set.not_infinite]
  by_contra hinf
  obtain ⟨S, hS⟩ := hinf.exists_subset_card_eq (r + 1)
  have hS₀ : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rw [ne_eq]
    rw [← Finset.card_eq_zero]
    rw [hS.2]
    omega

  have Simage : ∀ s : ℝ, ∃ k, s ∈ S → s = b k := by
    intro s
    by_cases hs : s ∈ S
    · apply hS.1 at hs
      obtain ⟨k, hk⟩ := hs
      use k
      intro _
      rw [hk]
    · use 0
      intro hs'
      contradiction
  choose i hi using Simage

  -- Let us apply the first claim to $k=i_{1}, \ldots, i_{r+1}$ and $\ell=\max \left\{i_{1}, \ldots, i_{r+1}\right\}$;
  replace h := rep_gap hr h
  let l := S.sup' hS₀ i

  -- we obtain that for every $j \in\{1, \ldots, r+1\}$ there exists $t_{j} \in[s, s+r-1]$ such that $b_{t_{j}}=b_{i_{j}}$.
  have (s : ℝ) : ∃ t : ℕ, s ∈ S → t ∈ Finset.Icc l (l + r - 1) ∧ b t = b (i s) := by
    by_cases hs : s ∈ S
    · obtain ⟨t,ht⟩ := h (i s) l (Finset.le_sup' i hs)
      use t
      intro _
      exact ht
    · use 0
      intro hs'
      contradiction

  -- Thus the segment $[s, s+r-1]$ should contain $r+1$ distinct integers, which is absurd.
  choose t ht using this
  suffices ∃ s₁ ∈ S, ∃ s₂ ∈ S, s₁ ≠ s₂ ∧ t s₁ = t s₂ by
    obtain ⟨s₁, hs₁, s₂, hs₂, hs⟩ := this
    absurd hs.1
    rw [hi s₁ hs₁, hi s₂ hs₂]
    rw [← (ht s₁ hs₁).2]
    rw [← (ht s₂ hs₂).2]
    congr 1
    exact hs.2

  apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to
  show (Finset.Icc l (l + r - 1)).card < _
  · simp [hS.2]
    omega
  · intro s hs
    exact (ht s hs).1


/-
Let $r$ be a positive integer, and let $a_{0}, a_{1}, \ldots$ be an infinite sequence of real numbers. Assume that for all nonnegative integers $m$ and $s$ there exists a positive integer $n \in[m+1, m+r]$ such that  $$ a_{m}+a_{m+1}+\cdots+a_{m+s}=a_{n}+a_{n+1}+\cdots+a_{n+s} $$  Prove that the sequence is periodic, i. e. there exists some $p \geqslant 1$ such that $a_{n+p}=a_{n}$ for all $n \geqslant 0$.  (India) -/
theorem algebra_24360 (r : ℕ) (a : ℕ → ℝ) (hr : 0 < r) (h : ∀ m s : ℕ, ∃ n : ℕ, n ∈ Finset.Icc (m + 1) (m + r) ∧ ∑ i ∈ Finset.range (s + 1), a (m + i) = ∑ i ∈ Finset.range (s + 1), a (n + i)) : ∃ p : ℕ, 1 ≤ p ∧ Function.Periodic a p := by

  -- For every indices $m \leqslant n$ we will denote $S(m, n)=a_{m}+a_{m+1}+\cdots+a_{n-1}$.
  set S : ℕ → ℕ → ℝ := fun m n => ∑ i ∈ Finset.range (n - m), a (m + i)

  -- By reindexing, we have the following equality among partial sums.
  have lemS (l m n : ℕ) : l ≤ m → m ≤ n → S l m + S m n = S l n := by
    intro hl hm
    simp [S]
    suffices ∑ i ∈ Finset.range (n - m), a (m + i) = ∑ i ∈ Finset.Ico (m - l) (n-l), a (l + i) by
      rw [this]
      apply Eq.symm
      suffices Finset.range (n - l) = Finset.range (m - l) ∪ Finset.Ico (m - l) (n - l) by
        rw [this]
        apply Finset.sum_union
        rw [Finset.disjoint_iff_inter_eq_empty, Finset.range_eq_Ico, Finset.Ico_inter_Ico]
        simp only [zero_le, sup_of_le_right, inf_le_left, Finset.Ico_eq_empty_of_le, S]
      rw [Finset.range_eq_Ico]
      rw [← Finset.Ico_union_Ico_eq_Ico]
      repeat omega
    apply Finset.sum_nbij' (fun i ↦ m - l + i) (fun j ↦ j - (m - l))
    · intro i hi
      simp at hi ⊢
      omega
    · intro j hj
      simp at hj ⊢
      omega
    · intro i _
      omega
    · intro j hj
      simp at hj
      omega
    · intro i hi
      congr 1
      omega

  -- Setting $s=0$ in the problem condition, we see that the sequence $\left(a_{i}\right)$ satisfies the condition of the lemma, thus it attains at most $r$ distinct values.
  have a_range_finite : Set.Finite (Set.range a) := by
    apply range_finite
    exact hr
    peel 1 h with m h
    convert h 0 using 4
    · simp
    · simp

  -- Denote by $A_{i}$ the ordered $r$-tuple $\left(a_{i}, \ldots, a_{i+r-1}\right)$; then among $A_{i}$ 's there are at most $r^{r}$ distinct tuples.
  let A : ℕ → Fin r → ℝ := fun n ↦ fun i ↦ a (n + i)

  have A_range_finite : Set.Finite (Set.range A) := by
    apply Set.Finite.subset
    apply Set.Finite.pi (t := fun i ↦ Set.range a)
    · intro _
      exact a_range_finite
    · rw [Set.range_subset_iff]
      intro n
      simp

  -- So for every $k \geqslant 0$ two of the tuples $A_{k}, A_{k+1}, \ldots, A_{k+r^{r}}$ are identical.
  -- This means that there exists a positive integer $p \leqslant r^{r}$ such that the equality $A_{d}=A_{d+p}$ holds infinitely many times.
  have hpD : ∃ p : ℕ, 0 < p ∧ { d : ℕ | A (d + p) = A d}.Infinite := by
    let R := A_range_finite.toFinset.card + 1
    let D := { d : ℕ | ∃ p ∈ Finset.Icc 1 R, A (d + p) = A d}
    suffices D.Infinite by
      rw [← Set.infinite_coe_iff] at this
      have hD : ∀ d : Set.Elem D, ∃ p : Set.Elem (Finset.Icc 1 R : Set ℕ), A (d + p) = A d := by
        intro ⟨d,hd⟩
        obtain ⟨p, hp⟩ := hd
        use ⟨p, hp.1⟩
        dsimp
        exact hp.2
      choose f hf using hD
      obtain ⟨p, hp⟩ := Finite.exists_infinite_fiber f
      use p.val
      constructor
      · have := p.prop
        simp at this
        omega
      · rw [Set.infinite_coe_iff] at hp
        apply Set.Infinite.mono
        show Subtype.val '' (f ⁻¹' {p}) ⊆ _
        · simp
          intro d
          simp
          intro hdp
          convert hf d
          rw [hdp]
        · apply Set.Infinite.image
          · intro x _ y _
            exact Subtype.eq
          · exact hp
    suffices ∀ k : ℕ, ∃ d : ℕ, d ∈ Finset.Ioc (k * R) ((k + 1) * R) ∧ ∃ p ∈ Finset.Icc 1 R, A (d + p) = A d by
      choose f hf using this
      apply Set.infinite_of_injective_forall_mem (?_ : f.Injective)
      · intro x
        exact (hf x).2
      · intro x y _
        have hx := (hf x).1
        have hy := (hf y).1
        simp at hx hy
        apply le_antisymm
        · suffices x * R < (y + 1) * R by
            nlinarith
          linarith
        · suffices y * R < (x + 1) * R by
            nlinarith
          linarith
    intro k
    suffices ∃ x ∈ Finset.Ioc (k * R) ((k + 1) * R), ∃ y ∈ Finset.Ioc (k * R) ((k + 1) * R), x ≠ y ∧ A x = A y by
      obtain ⟨x,hx,y,hy,hxy⟩ := this
      wlog hl : x < y generalizing x y
      · apply this y hy x hx
        constructor
        · exact hxy.1.symm
        · exact hxy.2.symm
        · omega
      use x
      constructor
      · exact hx
      use y - x
      simp
      split_ands
      · omega
      · simp at hx hy
        apply le_trans hy.2
        rw [add_mul, one_mul, add_comm, add_le_add_iff_left]
        exact hx.1.le
      · rw [hxy.2]
        apply congrArg
        omega
    apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    · show A_range_finite.toFinset.card < _
      simp [add_mul, R]
    · simp

  obtain ⟨p,hp,hD⟩ := hpD
  use p
  constructor
  · exact hp

  -- Let $D$ be the set of indices $d$ satisfying this relation.
  let memD (d : ℕ) := A (d + p) = A d

  suffices ∀ d : ℕ , memD d by
    intro d
    repeat rw [(by simp [A]: ∀ n, a n = A n ⟨0, hr⟩)]
    apply congrFun
    apply this

  -- Now we claim that $D$ coincides with the set of all nonnegative integers. Since $D$ is unbounded, it suffices to show that $d \in D$ whenever $d+1 \in D$.
  apply Nat.decreasing_induction_of_infinite

  · intro d hd
    -- For that, denote $b_{k}=S(k, p+k)$. The sequence $b_{0}, b_{1}, \ldots$ satisfies the lemma conditions, so there exists an index $t \in[d+1, d+r]$ such that $S(t, t+p)=S(d, d+p)$.
    let b := fun k ↦ S k (k + p)
    replace h : ∀ m : ℕ, ∃ n ∈ Finset.Icc (m + 1) (m + r), b m = b n := by
      peel 1 h with m h
      convert h (p - 1) using 4
      · simp [b,S]
        congr
        omega
      · simp [b,S]
        congr
        omega
    obtain ⟨t,ht,ht'⟩ := rep_gap hr h d (d + 1) (by omega : _)
    simp at ht

    -- This last relation rewrites as $S(d, t)=S(d+p, t+p)$.
    replace ht' : S d t = S (d + p) (t + p) := by
      simp [b] at ht'
      have : S d t + S t (t + p) = S d (t + p) := by
        apply lemS
        repeat omega
      have : S d (d + p) + S (d + p) (t + p) = S d (t + p) := by
        apply lemS
        repeat omega
      linarith

    -- Since $A_{d+1}=A_{d+p+1}$, we have $S(d+1, t)=S(d+p+1, t+p)$.
    have hd' : S (d + 1) t = S (d + 1 + p) (t + p) := by
      simp only [S]
      apply Eq.symm
      apply Finset.sum_congr
      · congr 1
        omega
      · intro i hi
        replace hi : i < r := by
          simp at hi
          omega
        suffices ∀ l, a (l + i) = A l ⟨i,hi⟩ by
          rw [this (d + 1), this (d + 1 + p)]
          apply congrFun
          exact hd
        simp [A]

    -- Therefore we obtain $$ a_{d}=S(d, t)-S(d+1, t)=S(d+p, t+p)-S(d+p+1, t+p)=a_{d+p} $$ and thus $A_{d}=A_{d+p}$, as required.
    suffices a (d + p) = a d by
      simp [memD, A]
      funext ⟨i,hi⟩
      dsimp
      by_cases hi' : i = 0
      · rw [hi']
        assumption
      · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hi'
        rw [(by omega : d + p + i = d + 1 + p + j)]
        rw [(by omega : d + i = d + 1 + j )]
        replace hj : j < r := by
          linarith
        rw [(by simp only [A] : a (d + 1 + j) = A (d + 1) ⟨j, hj⟩)]
        rw [(by simp only [A] : a (d + 1 + p + j) = A (d + 1 + p) ⟨j, hj⟩)]
        apply congrFun
        assumption
    suffices S d t - S (d + 1) t = S (d + p) (t + p)- S (d + 1 + p) (t + p) by
      rw [← lemS d (d + 1) t ?_ ?_] at this
      rw [← lemS (d + p) (d + 1 + p) (t + p) ?_ ?_] at this
      simp at this
      have lemS' : ∀ m, S m (m + 1) = a m := by
        simp [S]
      rw [← lemS' (d+ p)]
      rw [← lemS' d]
      rw [this]
      congr 1
      repeat omega
    rw [hd', ht']

  · exact hD
  -- Finally, we get $A_{d}=A_{d+p}$ for all $d$, so in particular $a_{d}=a_{d+p}$ for all $d$, QED.