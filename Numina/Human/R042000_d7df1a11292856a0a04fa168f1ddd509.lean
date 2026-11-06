import Mathlib

/- Ein Pirat möchte einen Schatz, bestehend aus 1000 Goldmünzen, die jeweils mindestens 1 g und zusammen genau 2 kg wiegen, in zwei Teile aufteilen, die in ihrer Masse jeweils um höchstens 1 g von 1 kg abweichen. Beweisen Sie, dass dies möglich ist. -/
theorem number_theory_605319 (s : ℕ → ℝ) (hs1 : ∀ n < 1000, 1 ≤ s n) (hs2 : ∑ n ∈ Finset.range 1000, s n = 2000) (hs3 : StrictMono s):
    ∃ s1 ⊆ Finset.range 1000, |(∑ i ∈ s1, s i) - 1000| ≤ 1 := by
  -- Let the masses of the 1000 coins in grams, in ascending order, be denoted by $m_{1} \leq m_{2} \leq \cdots \leq m_{1000}$. 
  -- We now prove by induction on $\ell=1, \ldots, 1000$ the following statement. 
  -- Lemma. For all $1 \leq \ell \leq 1000$ and every real number $0 \leq x \leq 2+\sum_{i=1}^{\ell} m_{i}$, there exists a (potentially empty) subset $I \subset\{1,2, \ldots, \ell\}$ such that $\sum_{i \in I} m_{i} \in[x-2, x]$ holds.
  have h1 : ∀ l ∈ Finset.range 1000, ∀ x, 0 ≤ x → x ≤ 2 + ∑ i ∈ Finset.range (l+1), s i → ∃ I ⊆ Finset.range (l+1), (x-2 ≤ ∑ i ∈ I, s i ∧ ∑ i ∈ I, s i ≤ x):= by
    intro l hl
    -- It holds that $x_{1} \leq 2000 / 1000=2$, so the base case $\ell=1$ is clear:
    have h2 : s 0 ≤ 2 := by
      by_contra!
      have : ∑ i ∈ Finset.range 1000, 2 < ∑ i ∈ Finset.range 1000, s i := by
        apply Finset.sum_lt_sum
        intro i hi
        have : s 0 ≤ s i := by
          by_cases h : i = 0
          · rw [h]
          have h3 : s 0 < s i := by
            apply StrictMono.imp hs3
            omega
          linarith
        linarith
        use 0 ;simp [this]
      simp at this;linarith
    induction l with 
    | zero => 
      intro x hx1 hx2
      by_cases h : x ≤ 2 
      · use ∅ ;simp [h,hx1]
      use {0} ;simp at hx2 ;simp ;constructor ;linarith ;linarith
    -- 考虑 \( x \leq 2 + \sum_{i=1}^{\ell+1} m_i \)。若 \( x \leq 2 + \sum_{i=1}^{\ell} m_i \)，直接应用归纳假设。否则，设 \( x' = x - m_{\ell+1} \)，由归纳假设存在子集 \( I' \subset \{1, \ldots, \ell\} \) 使得 \( \sum_{i \in I'} m_i \in [x'-2, x'] \)。取 \( I = I' \cup \{\ell+1\} \)，则 \( \sum_{i \in I} m_i \in [x-2, x] \)。
    | succ l ih => 
      intro x hx1 hx2
      have h3 : l ∈ Finset.range 1000 := by simp ;simp at hl ;linarith
      by_cases h : x ≤ 2 + ∑ i ∈ Finset.range (l + 1), s i
      · have h4 := ih h3 x hx1 h
        rcases h4 with ⟨I,hI,hI'⟩
        use I ;constructor
        · have : Finset.range (l + 1) ⊆ Finset.range (l + 1 + 1) := by
            apply Finset.range_subset.mpr
            simp
          exact subset_trans hI this
        exact hI'
      let x' := x-s (l+1)
      have h5 : x' ≤ 2+∑ i ∈ Finset.range (l+1), s i:= by 
        simp only [x']
        rw [Finset.sum_range_succ] at hx2
        linarith
      -- if $x2+\ell$ for all $\ell+1 \leq i \leq 1000$, which implies the following equality.
      -- $$ 2000=\sum_{i=1}^{1000} m_{i}=\sum_{i=1}^{\ell} m_{i}+\sum_{i=\ell+1}^{1000} m_{i}&gt;\ell+(1000-\ell)(2+\ell)=2000+999 \ell-\ell^{2} $$
      --It follows that $\ell&gt;999$, a contradiction, which completes the proof of the lemma.
      have h6 : 0 ≤ x':= by
        by_contra! h'
        simp only [x'] at h'
        have h7 : x < s (l+1) := by linarith
        simp at h
        have h8 : ∑ i ∈ Finset.range (l + 1), 1 ≤ ∑ i ∈ Finset.range (l + 1), s i := by
          apply Finset.sum_le_sum
          intro i hi
          apply hs1
          simp at hi ;simp at hl;linarith
        simp at h8
        have h9 : Finset.range 1000 = Finset.range (l+1) ∪ Finset.Icc (l+1) 999 := by
          apply Finset.ext ;intro a
          simp ;constructor
          · intro h'
            by_cases ha : a < l+1
            · left ;exact ha
            right ;omega
          intro h' ;rcases h' with h'|h' ;simp at hl ;linarith ;linarith
        have h10 : ∑ i ∈ Finset.Icc (l+1) 999, (2 + ((↑l:ℝ) + 1)) < ∑ i ∈ Finset.Icc (l+1) 999, s i := by
          apply Finset.sum_lt_sum
          intro i hi
          have : s (l+1) ≤ s i := by
           by_cases ht : (l+1) = i
           · rw [ht]
           simp at hi
           have ht : l+1 < i := by omega
           have ht' := StrictMono.imp hs3 ht
           linarith
          linarith
          use (l+1) ;simp ;simp at hl ;constructor ;omega ;linarith
        simp at h10
        rw [h9,Finset.sum_union] at hs2
        have : ((↑l:ℝ) + 1) + ↑(999 - l) * 2 + (↑(999 - l) * ↑l + ↑(999 - l)) < 2000 := by linarith
        simp at h3
        have this' : l ≤ 998 := by simp at hl ;linarith
        have this'' : l ≤ 999 := by linarith
        simp [this''] at this
        ring_nf at this
        by_cases hl' : l ≤ 997
        · have : 0 ≤ (↑l:ℝ) * 997 - ↑l ^ 2 := by 
            simp [pow_two]
            by_cases h : 0 < (↑l:ℝ)
            apply (mul_le_mul_left h).mpr ;simp ;linarith
            simp at h ;rw [h] ;simp
          linarith
        simp at hl'
        interval_cases l ;norm_num at this
        apply Finset.disjoint_left.mpr
        intro a ;simp ;intro ha1 ha2 ;linarith
      have h7 := ih h3 x' h6 h5
      rcases h7 with ⟨I,hI,hI'⟩
      use insert (l+1) I
      constructor
      · apply Finset.insert_subset
        simp
        have : Finset.range (l + 1) ⊆ Finset.range (l + 1 + 1) := by
            apply Finset.range_subset.mpr
            simp
        exact subset_trans hI this
      have h8 : (l+1) ∉ I := by
        by_contra!
        have : l+1 ∈ Finset.range (l + 1) := hI this
        simp at this
      have h9 : x = s (l+1) + x' := by simp [x']
      simp [Finset.sum_insert h8,h9]
      constructor
      · linarith
      linarith
  -- We now apply the lemma to $\ell=1000$ and $x=1001$. This shows that there exists a subset $I \subset\{1,2, \ldots, 1000\}$ such that $\sum_{i \in I} x_{i} \in[999,1001]$. Since $\sum_{i=1}^{1000} m_{i}=$ 2000, it also holds that $\sum_{i \in\{1, \ldots, 1000\} \backslash I} x_{i} \in[999,1001]$, and the partition of the coins corresponding to the decomposition
  -- $$ \{1, \ldots, 1000\}=I \cup(\{1, \ldots, 1000\} \backslash I) $$
  -- satisfies the claim.
  specialize h1 999 (by norm_num) 1001 (by norm_num)
  norm_num at h1
  rw [hs2] at h1
  norm_num at h1
  rcases h1 with ⟨I,hI,hI',hI''⟩
  use I
  simp [hI]
  apply abs_le.mpr
  constructor
  simp ;linarith
  simp ;linarith
      
  