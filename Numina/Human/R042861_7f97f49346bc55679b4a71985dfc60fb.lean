import Mathlib
open Real

/- Let $a_{1}, \ldots, a_{r}$ be positive real numbers. For $n>r$, we inductively define  $$ a_{n}=\max _{1 \leq k \leq n-1}\left(a_{k}+a_{n-k}\right) $$  Prove that there exist positive integers $\ell \leq r$ and $N$ such that $a_{n}=a_{n-\ell}+a_{\ell}$ for all $n \geq N$. (Iran) -/
theorem algebra_23926
    (r : ℕ)
    (hrpos : r > 0)
    (a : ℕ → ℝ)
    (hapos : ∀ i ∈ Finset.Icc 1 r, 0 < a i)
    (h : ∀ n > r, a n = sSup {a k + a (n - k) | k ∈ Finset.Ico 1 n}) :
    ∃ ℓ N, ℓ ∈ Finset.Icc 1 r ∧ ∀ n > N, a n = a (n - ℓ) + a ℓ := by

  -- simplify condition h
  have hhab {n : ℕ} (hn : n > r) : ((Finset.Ico 1 n).image (fun k => a k + a (n - k))).Nonempty := by
    use a 1 + a (n - 1); simp
    use 1; simp
    exact Nat.lt_of_le_of_lt hrpos hn
  have h {n : ℕ} (hn : n > r) : a n = ((Finset.Ico 1 n).image (fun k => a k + a (n - k))).max' (hhab hn) := by
    simp [h n hn]
    have hbdd : BddAbove {x | ∃ k, (1 ≤ k ∧ k < n) ∧ a k + a (n - k) = x} := by
      have : ((Finset.Icc 1 n).image a).Nonempty := by
        use a 1
        simp
        use 1
        simp
        exact Nat.one_le_of_lt hn
      use ((Finset.Icc 1 n).image a).max' this + ((Finset.Icc 1 n).image a).max' this
      refine mem_upperBounds.mpr ?_
      intro x hx
      simp at hx
      obtain ⟨k, hk, hx⟩ := hx
      rw [←hx]
      apply add_le_add
      · apply Finset.le_max'
        simp
        use k
        simp [hk.1]
        exact le_of_lt hk.2
      · apply Finset.le_max'
        simp
        use n - k
        simp
        apply Nat.le_sub_of_add_le
        rw [add_comm]
        apply Nat.add_one_le_of_lt hk.2
    have hne : {x | ∃ k, (1 ≤ k ∧ k < n) ∧ a k + a (n - k) = x}.Nonempty := by
      use a 1 + a (n - 1); simp; use 1; simp; exact Nat.lt_of_le_of_lt hrpos hn
    apply le_antisymm
    · apply csSup_le_iff hbdd hne|>.mpr
      intro b hb
      simp at hb
      obtain ⟨k, hk, hb⟩ := hb
      rw [←hb]
      apply Finset.le_max'
      simp; use k, hk
    · apply le_csSup_iff hbdd hne |>.mpr
      intro b hb
      apply Finset.max'_le
      intro r hr
      simp at hr
      obtain ⟨k, hk, hr⟩ := hr
      rw [←hr]
      apply mem_upperBounds.mp hb
      use k

  -- First, from the problem conditions we have that each $a_{n}(n&gt;r)$ can be expressed as
  -- $a_{n}=a_{j_{1}}+a_{j_{2}}$ with $j_{1}, j_{2}&lt;n, j_{1}+j_{2}=n$.
  have han_eq_2 {n : ℕ} (hn : n > r) : ∃ j₁ j₂, j₁ ∈ Finset.Ico 1 n ∧ j₂ ∈ Finset.Ico 1 n ∧ j₁ + j₂ = n ∧ a n = a j₁ + a j₂ := by
    rw [h hn]
    obtain h := Finset.max'_mem _ (hhab hn)
    simp at h
    obtain ⟨k, ⟨hk1, hk2⟩, h⟩ := h
    use k, n - k
    simp [h, hk2, Nat.add_sub_cancel' (le_of_lt hk2), hk1]
    split_ands
    · exact Nat.le_sub_of_add_le' hk2
    · exact Nat.zero_lt_of_lt hn
    · exact hk1

  -- $$ On the other hand, suppose that the indices $i_{1}, \ldots, i_{k}$ satisfy the conditions
  -- $$ 1 \leq i_{j} \leq r, \quad i_{1}+\cdots+i_{k}=n, \quad i_{1}+i_{2}&gt;r .
  let pred_index (n k : ℕ) (hk : k > 1) (i : ℕ → ℕ) (supp : Finset ℕ) : Prop := i.support = supp ∧ supp.card = k ∧ 0 ∈ supp ∧ 1 ∈ supp ∧
      (∀ α ∈ supp, i α ∈ Finset.Icc 1 r) ∧ ∑ α ∈ supp, i α = n ∧ i 0 + i 1 > r

  -- If, say, $j_{1}&gt;r$ then we can proceed in the same way with $a_{j_{1}}$, and so on.
  -- Finally, we represent $a_{n}$ in a form $$ \begin{gathered} a_{n}=a_{i_{1}}+\cdots+a_{i_{k}}, \ 1 \leq i_{j} \leq r, \quad i_{1}+\cdots+i_{k}=n . \end{gathered} $$
  -- Moreover, if $a_{i_{1}}$ and $a_{i_{2}}$ are the numbers in (2) obtained on the last step, then $i_{1}+i_{2}&gt;r$.
  -- Hence we can adjust (3) as $$ 1 \leq i_{j} \leq r, \quad i_{1}+\cdots+i_{k}=n, \quad i_{1}+i_{2}&gt;r .
  have han_eq_k {n : ℕ} (hn : n > r) : ∃ (k : ℕ) (hk : k > 1) (i : ℕ → ℕ) (supp : Finset ℕ), pred_index n k hk i supp ∧ a n = ∑ α ∈ supp, a (i α) := by
    induction n using Nat.strongRecOn
    rename_i n ih
    obtain ⟨j₁, j₂, h₁, h₂, hadd, han⟩ := han_eq_2 hn
    by_cases hj₁ : j₁ ≤ r
    · by_cases hj₂ : j₂ ≤ r
      · use 2, (by simp)
        let i (x : ℕ) := if x = 0 then j₁ else if x = 1 then j₂ else 0
        let supp : Finset ℕ := {0, 1}
        use i, supp
        constructor
        · split_ands
          · ext x
            simp [i, supp]
            constructor <;> intro h
            · by_cases h' : x = 0
              · simp [h']
              · simp [h'] at h
                by_cases h'' : x = 1
                · simp [h'']
                · simp [h''] at h
            · rcases h with h | h <;> simp [h]
              · simp at h₁; apply ne_of_gt; exact h₁.1
              · simp at h₂; apply ne_of_gt; exact h₂.1
          · simp [supp]
          · simp [supp]
          · simp [supp]
          · intro x hx
            simp [supp] at hx
            rcases hx with h | h <;> simp [h, i]
            · simp at h₁
              simp [h₁.1, hj₁]
            · simp at h₂
              simp [h₂.1, hj₂]
          · simp [supp, i, hadd]
          · simp [i, hadd]
            exact hn
        · simp [supp, i, han]
      · simp at hj₂
        have : j₂ < n := by simp [←hadd]; simp at h₁; exact h₁.1
        obtain ⟨k, hk, i, supp, hpred, hsum⟩ := ih j₂ this hj₂
        have hne : supp.Nonempty := by use 0; simp [hpred.2.2.1]
        let ub := supp.max' hne + 1
        let i' (x : ℕ) := if x = ub then j₁ else i x
        let supp' := supp ∪ {ub}
        have hnmem : ub ∉ supp := by intro h; apply Finset.le_max' at h; simp [ub] at h
        use k + 1, (by simp; exact Nat.zero_lt_of_lt hk), i', supp'
        constructor
        · split_ands
          · ext x
            simp [i', supp']
            constructor <;> intro h
            · by_cases h' : x = ub
              · simp [h']
              · simp [h'] at h
                apply Function.mem_support.mpr at h
                rw [hpred.1] at h
                right; exact h
            · by_cases h' : x = ub
              · simp [h']; simp at h₁; apply ne_of_gt; exact h₁.1
              · simp [h'] at h ⊢
                apply Function.mem_support.mp
                rw [hpred.1]
                exact h
          · simp [supp']
            rw [Finset.card_union_of_disjoint]
            simp [hpred.2.1]
            simp [hnmem]
          · simp [supp']; left; exact hpred.2.2.1
          · simp [supp']; left; exact hpred.2.2.2.1
          · simp [supp', i']
            intro α hα
            by_cases h : α = ub
            · simp only [if_pos h]
              simp at h₁
              constructor
              · exact h₁.1
              · exact hj₁
            · simp [h] at hα ⊢
              apply hpred.2.2.2.2.1 α at hα
              simp at hα
              exact hα
          · simp [supp', i']
            rw [Finset.sum_union, ←hadd, ←hpred.2.2.2.2.2.1]
            simp [add_comm j₁]
            apply Finset.sum_congr rfl
            intro x hx
            have : x ≠ ub := by intro h; rw [h] at hx; exact hnmem.elim hx
            simp [this]
            simp [hnmem]
          · simp [i']
            have h1 : ¬ 0 = ub := by intro h; rw [←h] at hnmem; exact hnmem.elim hpred.2.2.1
            have h2 : ¬ 1 = ub := by intro h; rw [←h] at hnmem; exact hnmem.elim hpred.2.2.2.1
            simp [h1, h2]
            exact hpred.2.2.2.2.2.2
        · simp [han, supp', i']
          have : ub ∉ supp := by intro h; apply Finset.le_max' at h; simp [ub] at h
          rw [Finset.sum_union]
          · simp [hsum, add_comm]
            apply Finset.sum_congr rfl
            intro x hx
            congr
            have : x ≠ ub := by intro h; simp [h] at hx; contradiction
            simp [this]
          · simp [this]
    · simp at hj₁
      have : j₁ < n := by simp [←hadd]; simp at h₂; exact h₂.1
      obtain ⟨k, hk, i, supp, hpred, hsum⟩ := ih j₁ this hj₁
      have hne : supp.Nonempty := by use 0; simp [hpred.2.2.1]
      let ub := supp.max' hne + 1
      by_cases hj₂ : j₂ ≤ r
      · let i' (x : ℕ) := if x = ub then j₂ else i x
        let supp' := supp ∪ {ub}
        use k + 1, (by simp; exact Nat.zero_lt_of_lt hk), i', supp'
        have hnmem : ub ∉ supp := by intro h; apply Finset.le_max' at h; simp [ub] at h
        constructor
        · split_ands
          · ext x
            simp [i', supp']
            constructor <;> intro h
            · by_cases h' : x = ub
              · simp [h']
              · simp [h'] at h
                apply Function.mem_support.mpr at h
                rw [hpred.1] at h
                right; exact h
            · by_cases h' : x = ub
              · simp [h']; simp at h₂; apply ne_of_gt; exact h₂.1
              · simp [h'] at h ⊢
                apply Function.mem_support.mp
                rw [hpred.1]
                exact h
          · simp [supp']
            rw [Finset.card_union_of_disjoint]
            simp [hpred.2.1]
            simp [hnmem]
          · simp [supp']; left; exact hpred.2.2.1
          · simp [supp']; left; exact hpred.2.2.2.1
          · simp [supp', i']
            intro α hα
            by_cases h : α = ub
            · simp only [if_pos h]
              simp at h₂
              constructor
              · exact h₂.1
              · exact hj₂
            · simp [h] at hα ⊢
              apply hpred.2.2.2.2.1 α at hα
              simp at hα
              exact hα
          · simp [supp', i']
            rw [Finset.sum_union, ←hadd, ←hpred.2.2.2.2.2.1]
            simp [add_comm j₁]
            apply Finset.sum_congr rfl
            intro x hx
            have : x ≠ ub := by intro h; rw [h] at hx; exact hnmem.elim hx
            simp [this]
            simp [hnmem]
          · simp [i']
            have h1 : ¬ 0 = ub := by intro h; rw [←h] at hnmem; exact hnmem.elim hpred.2.2.1
            have h2 : ¬ 1 = ub := by intro h; rw [←h] at hnmem; exact hnmem.elim hpred.2.2.2.1
            simp [h1, h2]
            exact hpred.2.2.2.2.2.2
        · simp [han, supp', i']
          have : ub ∉ supp := by intro h; apply Finset.le_max' at h; simp [ub] at h
          rw [Finset.sum_union]
          · simp [hsum]
            apply Finset.sum_congr rfl
            intro x hx
            congr
            have : x ≠ ub := by intro h; simp [h] at hx; contradiction
            simp [this]
          · simp [this]
      · simp at hj₂
        have : j₂ < n := by simp [←hadd]; simp at h₁; exact h₁.1
        obtain ⟨k', hk', i', supp', hpred', hsum'⟩ := ih j₂ this hj₂
        let i'' (x : ℕ) := if x < ub then i x else i' (x - ub)
        let supp'' : Finset ℕ := supp ∪ (supp'.image fun x => x + ub)
        have hdis : Disjoint supp (Finset.image (fun x ↦ x + ub) supp') := by
          refine Finset.disjoint_left.mpr ?h.right.a
          intro a ha
          apply Finset.le_max' at ha
          simp
          intro x _ h
          have : a ≥ ub := by simp [←h]
          have : ¬ a ≥ ub := by push_neg; simp [ub]; exact Order.lt_add_one_iff.mpr ha
          contradiction
        use k + k', (by exact Nat.lt_add_right k' hk), i'', supp''
        constructor
        · split_ands
          · ext x
            simp [i'', supp'']
            constructor <;> intro h
            · by_cases h' : x < ub
              · simp [h'] at h
                apply Function.mem_support.mpr at h
                rw [hpred.1] at h
                left; exact h
              · simp [h'] at h
                apply Function.mem_support.mpr at h
                rw [hpred'.1] at h
                right
                use x - ub, h
                simp at h'
                exact Nat.sub_add_cancel h'
            · by_cases h' : x < ub
              · simp [h']
                apply Function.mem_support.mp
                rw [hpred.1]
                rcases h with h | h
                · exact h
                · obtain ⟨y, _, h⟩ := h
                  simp [←h] at h'
              · simp [h']
                apply Function.mem_support.mp
                rw [hpred'.1]
                rcases h with h | h
                · apply Finset.le_max' at h
                  have : x < ub := by simp [ub]; exact Order.lt_add_one_iff.mpr h
                  exact h'.elim this
                · obtain ⟨y, hy, h⟩ := h
                  have : x - ub = y := by rw [←h]; apply Nat.add_sub_cancel
                  rw [this]
                  exact hy
          · simp [supp'']
            rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective]
            · rw [hpred.2.1, hpred'.2.1]
            · intro _ _ h
              simp at h
              exact h
            · exact hdis
          · simp [supp'']
            apply hpred.2.2.1
          · simp [supp'']
            left
            apply hpred.2.2.2.1
          · simp only [supp'', i'']
            intro α hα
            by_cases h : α < ub
            · simp only [if_pos h]
              apply hpred.2.2.2.2.1
              simp at hα
              rcases hα with h' | h'
              · exact h'
              · obtain ⟨a, _, ha'⟩ := h'
                simp [←ha'] at h
            · simp only [if_neg h]
              apply hpred'.2.2.2.2.1
              simp at hα
              rcases hα with h' | h'
              · apply Finset.le_max' at h'
                have : α < ub := by simp [ub]; exact Order.lt_add_one_iff.mpr h'
                exact h.elim this
              · obtain ⟨a, ha, ha'⟩ := h'
                have : α - ub = a := by rw [←ha']; apply Nat.add_sub_cancel
                rw [this]
                exact ha
          · simp [supp'', i'']
            rw [Finset.sum_union, Finset.sum_image]
            · rw [←hadd, ←hpred.2.2.2.2.2.1, ←hpred'.2.2.2.2.2.1]
              congr 1
              · apply Finset.sum_congr rfl
                intro x hx
                have : x < ub := by apply Finset.le_max' at hx; simp [ub]; exact Order.lt_add_one_iff.mpr hx
                simp [this]
              · apply Finset.sum_congr rfl
                simp
            · intro x _ y _ f
              apply Nat.add_right_cancel f
            · exact hdis
          · simp [i'']
            have : 1 < ub := by
              simp [ub]
              apply Nat.lt_of_add_one_le
              apply Finset.le_max'
              simp [hpred.2.2.2.1]
            simp [this]
            exact hpred.2.2.2.2.2.2
        · simp [han, supp'', i'']
          rw [Finset.sum_union]
          · rw [hsum, hsum']
            congr 1
            · apply Finset.sum_congr rfl
              intro x hx
              simp [supp''] at hx
              have : x < ub := by apply Finset.le_max' at hx; simp [ub]; exact Order.lt_add_one_iff.mpr hx
              simp [this]
            · rw [Finset.sum_image]
              · apply Finset.sum_congr rfl
                intro x _
                have : ¬ x + ub < ub := by simp
                simp [this]
              · intro x _ y _ f
                exact Nat.add_right_cancel f
          · exact hdis
  -- Then, denoting $s_{j}=i_{1}+\cdots+i_{j}$,
  -- from (1) we have $$ a_{n}=a_{s_{k}} \geq a_{s_{k-1}}+a_{i_{k}} \geq a_{s_{k-2}}+a_{i_{k-1}}+a_{i_{k}} \geq \cdots \geq a_{i_{1}}+\cdots+a_{i_{k}} $$
  have has {n : ℕ} (k : ℕ) (hk : k > 1) (i : ℕ → ℕ) (supp : Finset ℕ) (hi : pred_index n k hk i supp) (j : ℕ) :
      a (∑ α ∈ supp ∩ Finset.range (j + 1), i α) ≥ ∑ α ∈ supp ∩ Finset.range (j + 1), a (i α) := by
    have h0inter : supp ∩ {0} = {0} := by simp; exact hi.2.2.1
    induction j with
    | zero =>
      simp
      simp [h0inter]
    | succ j ih =>
      have hint : supp ∩ Finset.range (j + 1 + 1) = supp ∩ Finset.range (j + 1) ∪ (supp ∩ {j + 1}) := by
        rw [←Finset.inter_union_distrib_left]
        congr
        rw [Finset.range_succ]
        ext i; simp [or_comm]
      simp [hint]
      have hdis : Disjoint (supp ∩ Finset.range (j + 1)) (supp ∩ {j + 1}) := by
        refine Finset.disjoint_left.mpr ?succ.a
        intro a ha
        simp at ha ⊢
        simp [ha.1]
        exact ne_of_lt ha.2
      rw [Finset.sum_union hdis, Finset.sum_union hdis]
      by_cases hj : j + 1 ∈ supp
      · have : supp ∩ {j + 1} = {j + 1} := by exact Finset.inter_singleton_of_mem hj
        simp [this]
        trans a (∑ x ∈ supp ∩ Finset.range (j + 1), i x) + a (i (j + 1))
        · simp
          apply ih
        · have : ∑ x ∈ supp ∩ Finset.range (j + 1), i x + i (j + 1) > r := by
            apply lt_of_lt_of_le (hi.2.2.2.2.2.2)
            by_cases hj : j = 0
            · simp [hj, h0inter]
            · suffices h : i 0 + i 1 ≤ ∑ x ∈ supp ∩ Finset.range (j + 1), i x
              · exact Nat.le_add_right_of_le h
              · trans ∑ x ∈ {0, 1}, i x
                · simp
                · apply Finset.sum_le_sum_of_subset
                  intro x hx
                  simp at hx
                  rcases hx with h | h <;> simp [h]
                  · exact hi.2.2.1
                  · constructor
                    · exact hi.2.2.2.1
                    · exact Nat.zero_lt_of_ne_zero hj
          simp [h this]
          apply Finset.le_max'
          simp
          use i (j + 1)
          constructor
          · simp
            constructor
            · apply hi.2.2.2.2.1 (j + 1) at hj
              simp at hj
              exact hj.1
            · apply lt_of_lt_of_le  (b := i 0)
              · obtain h := hi.2.2.2.2.1 0 hi.2.2.1
                simp at h
                exact h.1
              · trans ∑ x ∈ {0}, i x
                · simp
                · apply Finset.sum_le_sum_of_subset
                  intro x hx
                  simp at hx
                  simp [hx]
                  exact hi.2.2.1
          · simp [add_comm]
      · have : supp ∩ {j + 1} = ∅ := by exact Finset.inter_singleton_of_not_mem hj
        simp [this]
        apply ih

  -- Summarizing these observations we get the following Claim.
  -- For every $n&gt;r$, we have $$ a_{n}=\max \left\{a_{i_{1}}+\cdots+a_{i_{k}}: \text { the collection }\left(i_{1}, \ldots, i_{k}\right) \text { satisfies }(4)\right\} $$
  have han_ge {n : ℕ} {k : ℕ} (hk : k > 1) (i : ℕ → ℕ) (supp : Finset ℕ) (h : pred_index n k hk i supp) : a n ≥ ∑ α ∈ supp, a (i α) := by
    have hne : supp.Nonempty := by use 0; simp [h.2.2.1]
    let ub := supp.max' hne
    obtain h' := has k hk i supp h ub
    have : supp ⊆ Finset.range (ub + 1) := by
      intro x hx
      apply Finset.le_max' at hx
      simp [ub]
      exact Order.lt_add_one_iff.mpr hx
    have : supp ∩ Finset.range (ub + 1) = supp := by exact Finset.inter_eq_left.mpr this
    simp [this, h.2.2.2.2.2.1] at h'
    exact h'
  -- Now we denote $$ s=\max _{1 \leq i \leq r} \frac{a_{i}}{i} $$
  let s := ((Finset.Icc 1 r).image (fun i => a i / i)).max' (by use a 1; simp; use 1; simp; exact hrpos)
  --and fix some index $\ell \leq r$ such that $s=\frac{a_{\ell}}{\ell}$.
  obtain ⟨ℓ, hℓ, hs⟩ : ∃ ℓ, ℓ ∈ Finset.Icc 1 r ∧ s = a ℓ / ℓ := by
    obtain h := Finset.max'_mem ((Finset.Icc 1 r).image (fun i => a i / i)) (by use a 1; simp; use 1; simp; exact hrpos)
    simp at h
    obtain ⟨k, hk, h⟩ := h
    simp
    use k, hk
    simp [h]
  use ℓ
  -- Consider some $n \geq r^{2} \ell+2 r$
  use r ^ 2 * ℓ + 2 * r, hℓ
  intro n hngt
  have hn_gt_r : n > r := by
    apply lt_trans ?_ hngt
    calc
      r < 2 * r := by exact lt_two_mul_self hrpos
      _ ≤ _ := by exact Nat.le_add_left (2 * r) (r ^ 2 * ℓ)
  -- and choose an expansion of $a_{n}$ in the form (2), (4).
  obtain ⟨k, hk, i, supp, ⟨hsupp, hcard, h0in, h1in, hipos, hsum, hgt⟩, heq⟩ := han_eq_k hn_gt_r
  wlog hext : ∃ α : ℕ, α ≥ 2 ∧ α ∈ supp ∧ i α = ℓ generalizing k i supp with H
  · -- Suppose that none of the numbers $i_{3}, \ldots, i_{k}$ equals $\ell$.
    simp at hext
    -- Then we have $n=i_{1}+\cdots+i_{k} \leq r k$,
    -- so $k \geq n / r \geq r \ell+2$.
    have hkgt : k > r * ℓ + 2 := by
      suffices : n ≤ r * k
      · apply lt_of_lt_of_le hngt at this
        apply Nat.lt_of_mul_lt_mul_left (a := r)
        apply lt_of_eq_of_lt ?_ this
        ring
      · rw [←hsum, show r * k = ∑ _ ∈ supp, r by simp [hcard]; ring]
        apply Finset.sum_le_sum
        intro _ h
        simp at hipos
        apply (hipos _ h).2
    -- Then by the pigeonhole principle there is an index $1 \leq j \leq r$ which appears among $i_{3}, \ldots, i_{k}$ at least $\ell$ times,
    -- and surely $j \neq \ell$.
    obtain ⟨j, hj, ind, hsub, hcardℓ, hind⟩ : ∃ j, j ∈ Finset.Icc 1 r ∧ ∃ ind : Finset ℕ, ind ⊆ supp ∧ ind.card = ℓ ∧ ∀ α ∈ ind, α ≥ 2 ∧ i α = j := by
      let t := (Finset.Icc 1 r).erase ℓ
      let s := supp \ {0, 1}
      have hf : ∀ a ∈ s, i a ∈ t := by
        intro a ha
        simp [s] at ha
        simp [t]
        have : a ≥ 2 := by
          by_contra
          interval_cases a
          all_goals simp at ha
        simp at hipos
        split_ands
        · apply hext a this ha.1
        · exact (hipos _ ha.1).1
        · exact (hipos _ ha.1).2
      have hb : t.card • ℓ < ↑s.card := by
        simp [s, t]
        rw [Finset.card_sdiff, Finset.card_erase_of_mem]
        · simp [hcard]
          calc
            (r - 1) * ℓ ≤ r * ℓ + 2 - 2 := by
              rw [Nat.add_sub_cancel]
              refine Nat.mul_le_mul ?h₁ ?h₂
              all_goals simp
            _ < k - 2 := by
              apply Nat.sub_lt_sub_right
              · exact Nat.le_add_left 2 (r * ℓ)
              · exact hkgt
        · exact hℓ
        · intro x hx
          simp at hx
          rcases hx with hx | hx <;> rw [hx]
          · exact h0in
          · exact h1in
      obtain ⟨y, hy, hcard⟩ := Finset.exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to (t := t) (s := s) (f := i) hf hb
      use y
      simp [t] at hy
      simp [hy.2]
      apply le_of_lt at hcard
      obtain ⟨ind, hsub, hcard⟩ := Finset.exists_subset_card_eq hcard
      use ind, ?_, hcard
      · intro α hα
        apply hsub at hα
        simp [s] at hα
        constructor
        · by_contra h
          interval_cases α
          all_goals simp at hα
        · exact hα.2
      · suffices h : ind ≤ supp
        exact h
        apply le_trans hsub
        intro x hx
        simp [s] at hx
        exact hx.1.1
    -- Let us delete these $\ell$ occurrences of $j$ from $\left(i_{1}, \ldots, i_{k}\right)$, and add $j$ occurrences of $\ell$ instead,
    have hjpos : j > 0 := by simp at hj; exact hj.1
    obtain ⟨up, hup⟩ : ∃ up, ∀ x ∈ supp, x < up := by
      have : supp.Nonempty := by
        apply Finset.card_pos.mp
        rw [hcard]
        exact Nat.zero_lt_of_lt hk
      use supp.max' this + 1
      intro x hx
      apply Nat.lt_add_one_of_le
      apply Finset.le_max'
      exact hx
    let i' (x : ℕ) := if x ∈ ind then 0 else (if x < up then i x else (if x < up + j then ℓ else 0))
    let supp' := supp \ ind ∪ Finset.Ico up (up + j)
    let k' := supp'.card
    have hdis : Disjoint (supp \ ind) (Finset.Ico up (up + j)) := by
      refine Finset.disjoint_iff_inter_eq_empty.mpr ?_
      suffices h : supp ∩ Finset.Ico up (up + j) = ∅
      · apply le_antisymm
        · simp [←h]
          refine Finset.inter_subset_inter_right ?_
          exact Finset.sdiff_subset
        · simp
      · refine Finset.eq_empty_of_forall_not_mem ?_
        intro x hx
        simp at hx
        have : ¬ up ≤ x := by
          push_neg
          apply hup
          exact hx.1
        exact this.elim hx.2.1
    have hk' : k' = k - ℓ + j := by
      simp [k', supp']
      simp [Finset.card_union_of_disjoint hdis]
      rw [Finset.card_sdiff hsub]
      simp [hcardℓ, hcard]
    have hk'gt : k' > 3 := by
      simp [hk']
      have hkgt : k > r * ℓ + 2 := by
        suffices : n ≤ r * k
        · apply lt_of_lt_of_le hngt at this
          apply Nat.lt_of_mul_lt_mul_left (a := r)
          apply lt_of_eq_of_lt ?_ this
          ring
        · rw [←hsum, show r * k = ∑ _ ∈ supp, r by simp [hcard]; ring]
          apply Finset.sum_le_sum
          intro _ h
          simp at hipos
          apply (hipos _ h).2
      have hℓ : ℓ ≤ r * ℓ := by exact Nat.le_mul_of_pos_left ℓ hrpos
      calc
        3 = 2 + 1 := by simp
        _ ≤ r * ℓ - ℓ + 2 + 1 := by simp
        _ = r * ℓ + 2 - ℓ + 1 := by simp; rw [Nat.sub_add_comm hℓ]
        _ ≤ r * ℓ + 2 - ℓ + j := by simp; simp at hj; exact hj.1
        _ < _ := by simp; refine Nat.sub_lt_sub_right ?_ hkgt; exact Nat.le_add_right_of_le hℓ
    have hi' : k' > 1 := by apply lt_trans ?_ hk'gt; simp
    -- obtaining a sequence $\left(i_{1}, i_{2}, i_{3}^{\prime}, \ldots, i_{k^{\prime}}^{\prime}\right)$ also satisfying (4).
    have hsuppeq :  Function.support i' = ↑supp' := by
      ext i
      simp [supp', i']
      constructor <;> intro h
      · simp [h.1]
        by_cases h1 : i < up
        · simp only [if_pos h1] at h
          obtain h := Function.mem_support.mpr h.2
          rw [hsupp] at h
          left
          exact h
        · simp only [if_neg h1] at h
          right
          push_neg at h1
          simp [h1]
          by_contra h2
          simp [if_neg h2] at h
      · rcases h with h | h
        · simp [h.2]
          have : i < up := by apply hup i h.1
          simp [this]
          apply Function.mem_support.mp
          rw [hsupp]
          exact h.1
        · have : ¬ i < up := by push_neg; exact h.1
          simp [this, h.2]
          constructor
          · intro h
            apply hsub at h
            apply hup i at h
            exact this.elim h
          · apply ne_of_gt
            simp at hℓ
            exact hℓ.1
    have h0in' : 0 ∈ supp' := by
      simp [supp']
      left
      constructor
      · exact h0in
      · intro h
        apply hind 0 at h
        simp at h
    have h1in' : 1 ∈ supp' := by
      simp [supp']
      left
      constructor
      · exact h1in
      · intro h
        apply hind 1 at h
        simp at h
    have hrin' : ∀ α ∈ supp', i' α ∈ Finset.Icc 1 r := by
      intro α hα
      simp [supp'] at hα
      simp only [i']
      rcases hα with hα | hα
      · simp only [if_neg hα.2]
        have : α < up := by apply hup α hα.1
        simp only [if_pos this]
        exact hipos α hα.1
      · have h1 : ¬ α < up := by push_neg; exact hα.1
        have : ¬ α ∈ ind := by intro h; apply hsub at h; apply hup α at h; exact h1.elim h
        simp only [if_neg this, if_neg h1, if_pos hα.2]
        exact hℓ
    have hsumeqn' : ∑ α ∈ supp', i' α = n := by
      have : ∑ α ∈ supp', (i' α) = ∑ α ∈ supp, (i α) + j * ℓ - ℓ * j := by
        simp [supp', i']
        rw [Finset.sum_union]
        · trans ∑ x ∈ supp, i x - ∑ _ ∈ ind, j + ∑ _ ∈ Finset.Ico up (up + j), ℓ
          · congr 1
            · rw [Finset.sum_ite]
              have h1 : Finset.filter (fun x => x ∈ ind) (supp \ ind) = ∅ := by
                ext x
                simp
              have h2 :  Finset.filter (fun x => x ∉ ind) (supp \ ind) = supp \ ind := by
                ext x
                simp
              simp [h1, h2]
              rw [Finset.sum_ite]
              have h1 : Finset.filter (fun x => x < up) (supp \ ind) = supp \ ind := by
                ext x
                simp
                intro hx _
                apply hup x hx
              have h2 : Finset.filter (fun x => x ≥ up) (supp \ ind) = ∅ := by
                ext x
                simp
                intro  hx _
                exact hup x hx
              simp [h1, h2]
              apply Nat.eq_sub_of_add_eq
              have : ind.card * j = ∑ x ∈ ind, i x := by
                trans ∑ _ ∈ ind, j
                · simp
                · apply Finset.sum_congr rfl
                  intro x hx
                  rw [(hind x hx).2]
              rw [this, Finset.sum_sdiff hsub]
            · apply Finset.sum_congr rfl
              intro α hα
              simp at hα
              have h1 : ¬ α < up := by push_neg; exact hα.1
              simp only [if_neg h1]
              have : ¬ α ∈ ind := by
                intro h
                apply hsub at h
                apply hup α at h
                exact h1.elim h
              simp only [if_neg this, if_pos hα.2]
          · rw [Finset.sum_const, Finset.sum_const, hcardℓ]
            simp
            rw [←Nat.sub_add_comm]
            rw [hsum]
            apply le_trans ?_ (le_of_lt hngt)
            apply le_add_of_le_left
            rw [mul_comm]
            apply Nat.mul_le_mul_right
            calc
              j ≤ r := by simp at hj; exact hj.2
              _ ≤ r ^ 2 := by apply Nat.le_self_pow; simp
        · exact hdis
      rw [this, hsum, mul_comm]
      simp
    have hi0i1 : i' 0 + i' 1 > r := by
      simp [i']
      have h1 : ¬ 0 ∈ ind := by intro h; apply hind 0 at h; simp at h
      have h2 : ¬ 1 ∈ ind := by intro h; apply hind 1 at h; simp at h
      simp [h1, h2]
      have h1 : 0 < up := by apply hup at h0in; exact h0in
      have h2 : 1 < up := by apply hup at h1in; exact h1in
      simp [h1, h2]
      exact hgt
    have hpred : pred_index n _ hi' i' supp' := by
      split_ands
      · exact hsuppeq
      · rfl
      · exact h0in'
      · exact h1in'
      · exact hrin'
      · exact hsumeqn'
      · exact hi0i1
    -- By Claim, we have $$ a_{i_{1}}+\cdots+a_{i_{k}}=a_{n} \geq a_{i_{1}}+a_{i_{2}}+a_{i_{3}^{\prime}}+\cdots+a_{i_{k^{\prime}}^{\prime}} $$ or,
    apply han_ge hi' i' at hpred
    rw [heq] at hpred
    have hsum' : ∑ α ∈ supp', a (i' α) = ∑ α ∈ supp, a (i α) + (j * a ℓ - ℓ * a j) := by
      simp [supp', i']
      rw [Finset.sum_union hdis]
      trans ∑ x ∈ supp, a (i x) - ∑ _ ∈ ind, a j + ∑ _ ∈ Finset.Ico up (up + j), a ℓ
      · congr 1
        · trans ∑ x ∈ supp \ ind, a (i x)
          · apply Finset.sum_congr rfl
            intro x hx
            simp at hx
            congr
            simp [hx.2]
            have : ¬ up ≤ x := by simp; apply hup x hx.1
            simp [this]
          · rw [Finset.sum_sdiff_eq_sub hsub]
            simp only [sub_right_inj]
            apply Finset.sum_congr rfl
            intro x hx
            congr
            rw [(hind x hx).2]
        · apply Finset.sum_congr rfl
          intro x hx
          simp at hx
          have : ¬ x < up := by push_neg; exact hx.1
          simp [this, hx.2]
          have : ¬ x ∈ ind := by intro h; apply hsub at h; apply hup x at h; exact this.elim h
          simp [this]
      · simp [hcardℓ]
        apply eq_of_sub_eq_zero
        ring
    -- after removing the coinciding terms, $\ell a_{j} \geq j a_{\ell}$, so $\frac{a_{\ell}}{\ell} \leq \frac{a_{j}}{j}$.
    have : a j / j ≥ a ℓ / ℓ := by
      rw [hsum'] at hpred
      simp at hpred
      apply div_le_div_iff₀ ?_ ?_ |>.mpr
      · rw [mul_comm, mul_comm (a j)]
        exact hpred
      · simp at hℓ; simp; exact hℓ.1
      · simp at hj ⊢
        exact hj.1
    -- By the definition of $\ell$, this means that $\ell a_{j}=j a_{\ell}$,
    have : a ℓ / ℓ = a j / j := by
      apply le_antisymm this
      rw [←hs]
      apply Finset.le_max'
      apply Finset.mem_image.mpr
      use j
    apply H _ hi' i' supp'
    · -- hence $$ a_{n}=a_{i_{1}}+a_{i_{2}}+a_{i_{3}^{\prime}}+\cdots+a_{i_{k^{\prime}}^{\prime}} $$.
      rw [heq, hsum']
      simp
      apply sub_eq_zero_of_eq
      calc
        _ = (a ℓ) / ℓ * ℓ * j := by rw [div_mul_cancel₀]; ring; simp at hℓ ⊢; apply ne_of_gt; exact hℓ.1
        _ = (a j) / j * j * ℓ := by rw [this]; ring
        _ = _ := by rw [div_mul_cancel₀]; ring; simp at hj ⊢; apply ne_of_gt; exact hj.1
    · exact hsuppeq
    · rfl
    · exact h0in'
    · exact h1in'
    · exact hrin'
    · exact hsumeqn'
    · exact hi0i1
    · use up
      split_ands
      · apply hup at h1in
        exact h1in
      · simp [supp']
        right
        exact hjpos
      · simp [i']
        have : ¬ up ∈ ind := by
          intro h
          apply hsub at h
          apply hup at h
          simp at h
        simp only [if_neg this]
        simp [hjpos]
  · obtain ⟨β, hβ, hinsupp, heq'⟩ := hext
    have han : a n = a ℓ + ∑ α ∈ supp.erase β, a (i α) := by simp [heq]; rw [Finset.sum_erase_eq_sub hinsupp, heq']; ring
    -- Thus, for every $n \geq r^{2} \ell+2 r$ we have found a representation of the form (2), (4) with $i_{j}=\ell$ for some $j \geq 3$.
    -- Rearranging the indices we may assume that $i_{k}=\ell$.
    let i' (α : ℕ) : ℕ := if α = β then 0 else i α
    let supp' := supp.erase β
    -- Finally, observe that in this representation, the indices $\left(i_{1}, \ldots, i_{k-1}\right)$
    -- satisfy the conditions (4) with $n$ replaced by $n-\ell$.
    have hkgt : k > r * ℓ + 2 := by
      suffices : n ≤ r * k
      · apply lt_of_lt_of_le hngt at this
        apply Nat.lt_of_mul_lt_mul_left (a := r)
        apply lt_of_eq_of_lt ?_ this
        ring
      · rw [←hsum, show r * k = ∑ _ ∈ supp, r by simp [hcard]; ring]
        apply Finset.sum_le_sum
        intro _ h
        simp at hipos
        apply (hipos _ h).2
    have hk_gt_3 : k > 3 := by
      apply lt_of_le_of_lt ?_ hkgt; simp
      suffices h : r * ℓ > 0
      · exact h
      · apply mul_pos hrpos
        simp at hℓ
        exact hℓ.1
    have hgt' : k - 1 > 1 := by apply Nat.lt_sub_of_add_lt; simp; exact Nat.lt_of_succ_lt hk_gt_3
    have hi' : pred_index (n - ℓ) _ hgt' i' supp' := by
      simp only [pred_index, i', supp']
      split_ands
      · ext α
        simp
        constructor <;> intro h
        · constructor
          · suffices h : α ∈ i.support
            · rw [hsupp] at h
              exact h
            · simp only [Function.mem_support, ne_eq]
              exact h.2
          · exact h.1
        · constructor
          · exact h.2
          · apply Function.mem_support.mp
            rw [hsupp]
            exact h.1
      · rw [Finset.card_erase_of_mem hinsupp, hcard]
      · simp [h0in]
        apply ne_of_lt
        exact Nat.zero_lt_of_lt hβ
      · simp [h1in]
        apply ne_of_lt
        exact hβ
      · intro α hα
        simp at hα
        simp only [if_neg hα.1]
        exact hipos α hα.2
      · have h : n - ℓ = ∑ α ∈ supp.erase β, (i α) := by
          apply Nat.sub_eq_of_eq_add
          rw [←heq', Finset.sum_erase_add, hsum]
          exact hinsupp
        rw [h]
        apply Finset.sum_congr rfl
        intro _ h
        simp at h
        simp [h.1]
      · have h1 : ¬ 0 = β := by apply ne_of_lt; apply lt_of_lt_of_le ?_ hβ; simp
        have h2 : ¬ 1 = β := by apply ne_of_lt; apply lt_of_lt_of_le ?_ hβ; simp
        simp [h1, h2]
        exact hgt
    -- Thus, from the Claim we get $$ a_{n-\ell}+a_{\ell} \geq\left(a_{i_{1}}+\cdots+a_{i_{k-1}}\right)+a_{\ell}=a_{n} $$
    have : ∑ α ∈ supp', a (i' α) ≤ a (n - ℓ) := by
      have : n - ℓ > r := by
        calc
          n - ℓ > r ^ 2 * ℓ + 2 * r - ℓ := by
            refine Nat.sub_lt_sub_right ?_ hngt
            trans r
            · simp at hℓ
              exact hℓ.2
            · calc
                r ≤ 2 * r := by refine Nat.le_mul_of_pos_left r ?_; simp
                _ ≤ _ := by exact Nat.le_add_left (2 * r) (r ^ 2 * ℓ)
          _ > r := by
            apply Nat.lt_sub_of_add_lt
            rw [add_comm]
            apply add_lt_add_of_le_of_lt
            · refine Nat.le_mul_of_pos_left ℓ ?h.h₁.h
              apply pow_pos hrpos
            · exact lt_two_mul_self hrpos
      apply han_ge
      · exact hi'
      · exact hgt'
    have hge : a (n - ℓ) + a ℓ ≥ a n := by
      rw [han, add_comm]
      trans a ℓ + ∑ α ∈ supp', a (i' α)
      · simp
        exact this
      · apply le_of_eq
        simp [supp', i']
        apply Finset.sum_congr rfl
        intro α hα
        simp at hα
        simp [hα.1]
    -- which by (1) implies $$ a_{n}=a_{n-\ell}+a_{\ell} \quad \text { for each } n \geq r^{2} \ell+2 r $$ as desired.
    apply le_antisymm hge
    rw [h hn_gt_r]
    apply Finset.le_max'
    simp at hℓ ⊢
    use ℓ
    split_ands
    · exact hℓ.1
    · exact lt_of_le_of_lt hℓ.2 hn_gt_r
    · ring
