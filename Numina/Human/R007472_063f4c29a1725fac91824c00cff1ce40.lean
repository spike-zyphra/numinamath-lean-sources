import Mathlib

open Finset Real


/- Soit $a_{1}, a_{2}, \ldots, a_{n}$ des entiers strictement positifs. Pour tout $k=1,2, \ldots, n$, on note

$$
m_{k}=\max _{1 \leq \ell \leq k} \frac{a_{k-\ell+1}+a_{k-\ell+2}+\cdots+a_{k}}{\ell} .
$$

Montrer que pour tout $\alpha>0$, le nombre d'entiers $k$ tel que $m_{k}>\alpha$ est strictement plus petit que $\frac{a_{1}+a_{2}+\cdots+a_{n}}{\alpha}$. -/
theorem inequalities_604973 {n : ℕ} (hn : 0 < n) (a : ℕ → ℤ)
    (ha : ∀ i ∈ Icc 1 n, 0 < a i) (m : ℕ → ℝ)
    (hm : ∀ k ∈ Icc 1 n, m k = sSup {((∑ i ∈ Icc 1 l, a (k - i + 1)) / (l : ℝ)) | l ∈ Icc 1 k}) :
    ∀ α > 0, {k | k ∈ Icc 1 n ∧ α < m k}.ncard < (∑ i ∈ Icc 1 n, a i) / α := by

  -- prove that if α < m k, then ∃ 1 ≤ l ≤ k such that l < (∑ i ∈ Icc 1 l, a (k - i + 1)) / α
  have lt_sSup (α : ℝ) (hαpos : α > 0) (k : ℕ) (hk : k ≥ 1) (hα : α < sSup {x | ∃ l ∈ Icc 1 k, (∑ i ∈ Icc 1 l, a (k - i + 1)) / (l : ℝ) = x}) :
      ∃ l ∈ Icc 1 k, l < (∑ i ∈ Icc 1 l, a (k - i + 1)) / α := by
    let ε := α - sSup {x | ∃ l ∈ Icc 1 k, (∑ i ∈ Icc 1 l, a (k - i + 1)) / (l : ℝ) = x}
    have hε : ε < 0 := by
      simp only [ε]
      exact sub_neg.mpr hα
    have : {x | ∃ l ∈ Icc 1 k, (∑ i ∈ Icc 1 l, a (k - i + 1)) / (l : ℝ) = x}.Nonempty := by
      use ∑ i ∈ Icc 1 1, a (k - i + 1) / (1 : ℝ), 1
      simp [hk]
    apply Real.add_neg_lt_sSup this at hε
    obtain ⟨x, ⟨⟨l, ⟨hl1, hl2⟩⟩, hx⟩⟩ := hε
    use l, hl1
    simp only [ε] at hx
    rw [add_sub_cancel, ←hl2] at hx
    apply lt_div_iff₀ (by norm_cast; simp at hl1; exact hl1.left) |>.mp at hx
    apply lt_div_iff₀ ?_ |>.mpr
    · rw [mul_comm]; exact hx
    · exact hαpos

  intro α hα
  -- let S be the set of k such that α < m k
  let S : Finset ℕ := Finset.filter (fun k => α < m k) (Icc 1 n)
  have : {k | k ∈ Icc 1 n ∧ α < m k}.ncard = S.card := by
    rw [show S.card = (S : Set ℕ).ncard by simp only [Set.ncard_coe_Finset]]
    congr
    ext k
    simp [S]
  rw[this]
  by_cases hS : S.Nonempty
  · -- if S is nonempty, let k be the maximum element of S
    let k := S.max' hS
    have hk : k ∈ S := by exact max'_mem S hS
    simp only [S, mem_filter] at hk
    obtain ⟨hk, hlt⟩ := hk
    simp only [hm k hk] at hlt
    simp at hk
    -- There exists $\ell_{1}$ such that $a_{k_{1}-\ell_{1}+1}+\cdots+a_{k_{1}}&gt;\ell_{1} \alpha$.
    apply lt_sSup α hα k hk.left at hlt
    obtain ⟨l, ⟨hl, hlt⟩⟩ := hlt

    -- prove a equivalent statement
    have htrans : ∑ i ∈ Icc 1 l, a (k - i + 1) = ∑ i ∈ Icc (k - l + 1) k, a i := by
      simp at hl
      let g (i : ℕ) := k - i + 1
      have himage : (Icc 1 l).image g = Icc (k - l + 1) k := by
        ext x
        simp [g]
        constructor <;> intro h
        · obtain ⟨a, ha⟩ := h
          rw [←ha.right]
          constructor
          · rel [ha.left.right]
          · rw [←tsub_tsub_assoc (le_trans ha.left.right hl.right) ha.left.left]
            exact Nat.sub_le k (a - 1)
        · use k - x + 1
          simp
          constructor
          · calc
              k - x + 1 ≤ k - (k - l + 1) + 1 := by rel [h.left]
              _ = l := by
                rw [Nat.sub_add_eq, Nat.sub_add_cancel, Nat.sub_sub_self hl.right]
                rw [Nat.sub_sub_self hl.right]
                exact hl.left
          · rw [Nat.sub_add_eq, Nat.sub_add_cancel, Nat.sub_sub_self h.right]
            rw [Nat.sub_sub_self h.right]
            calc
              1 ≤ k - l + 1 := by exact Nat.le_add_left 1 (k - l)
              _ ≤ x := by exact h.left
      rw [←himage, Finset.sum_image]
      intro x hx y hy hxy
      simp [g] at hxy
      simp at hx hy
      apply Nat.sub_eq_iff_eq_add' (le_trans hx.right hl.right) |>.mp at hxy
      rw [←Nat.add_sub_assoc (le_trans hy.right hl.right), eq_comm] at hxy
      have : y ≤ x + k := by
        rw [add_comm]
        apply Nat.le_add_right_of_le
        exact le_trans hy.right hl.right
      apply Nat.sub_eq_iff_eq_add' this |>.mp at hxy
      exact Nat.add_right_cancel hxy
    rw [htrans] at hlt

    by_cases hl' : l ≥ k
    · -- if l = k, then S.card ≤ l
      have : S.card ≤ (l : ℝ) := by
        simp [S]
        apply le_trans ?_ hl'
        suffices h : (filter (fun k ↦ α < m k) (Icc 1 n)) ⊆ Icc 1 k
        · rw [show k = (Icc 1 k).card by simp]
          exact card_le_card h
        · intro k'
          simp
          intro hk1 hkm hkα
          simp [hk1]
          have hkS : k' ∈ S := by simp [S]; exact ⟨⟨hk1, hkm⟩, hkα⟩
          exact le_max' S k' hkS
      -- l < (∑ i ∈ Icc 1 l, a (k - i + 1)) / α
      apply lt_of_le_of_lt this
      apply lt_of_lt_of_le hlt
      -- (∑ i ∈ Icc 1 l, a (k - i + 1)) / α ≤ (∑ i ∈ Icc 1 n, a i) / α
      apply div_le_div_of_nonneg_right
      · simp
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp at hi ⊢
          constructor
          · calc
              1 ≤ k - l + 1 := by exact Nat.le_add_left 1 (k - l)
              _ ≤ i := by exact hi.left
          · exact le_trans hi.right hk.right
        · intro i hi _
          apply le_of_lt
          norm_cast
          exact ha i hi
      · exact le_of_lt hα
    · -- if l < k, then we can apply the induction hypothesis
      simp at hl'
      let n' := k - l
      have hn' : n' > 0 := by
        simp [n']
        exact hl'
      have : n' < n := by
        simp [n']
        calc
          k - l < k := by
            apply Nat.sub_lt_self
            simp at hl
            exact hl.left
            exact Nat.le_of_succ_le hl'
          _ ≤ n := by exact hk.right
      have hnn' : n' ≤ n := by exact Nat.le_of_succ_le this
      have hsub : Icc 1 n' ⊆ Icc 1 n := by
        intro i hi
        simp at hi ⊢
        exact ⟨hi.1, le_trans hi.2 hnn'⟩
      have ha' (i : ℕ) (hi : i ∈ Icc 1 n') : 0 < a i := by
        apply ha
        exact hsub hi
      have hm' (k : ℕ) (hk : k ∈ Icc 1 n') : m k = sSup {((∑ i ∈ Icc 1 l, a (k - i + 1)) / (l : ℝ)) | l ∈ Icc 1 k} := by
        apply hm
        exact hsub hk
      obtain ih := inequalities_604973 hn' a ha' m hm' α hα
      -- note that S ⊆ {k | k ∈ Icc 1 n' ∧ α < m k} ∪ Icc (k - l + 1) k
      have h : (S.card : ℝ) ≤ {k | k ∈ Icc 1 n' ∧ α < m k}.ncard + l := by
        norm_cast
        have : {k | k ∈ Icc 1 n' ∧ α < m k}.ncard = (filter (fun k ↦ α < m k) (Icc 1 n')).card := by
          have : (filter (fun k ↦ α < m k) (Icc 1 n')).card = ((filter (fun k ↦ α < m k) (Icc 1 n')) : Set ℕ).ncard := by simp only [Set.ncard_coe_Finset]
          rw [this]
          congr
          ext k
          simp
        rw [this]
        suffices h : S ⊆ (filter (fun k ↦ α < m k) (Icc 1 n')) ∪ Icc (k - l + 1) k
        · apply Finset.card_le_card at h
          apply le_trans h
          apply le_trans (Finset.card_union_le _ _)
          simp
          rw [Nat.add_sub_cancel']
          exact Nat.le_of_succ_le hl'
        · intro k' hk'
          simp at hk' ⊢
          by_cases hle : k' ≤ n'
          · apply Or.inl
            simp [S] at hk'
            split_ands
            · exact hk'.1.1
            · exact hle
            · exact hk'.2
          · simp at hle
            apply Or.inr
            split_ands
            · simp [n'] at hle
              exact hle
            · apply le_max' S k'
              exact hk'
      apply lt_of_le_of_lt h
      -- it suffices to prove that {k | k ∈ Icc 1 n' ∧ α < m k}.ncard + l < (∑ i ∈ Icc 1 n, a i) / α
      calc
        {k | k ∈ Icc 1 n' ∧ α < m k}.ncard + (l : ℝ) < (∑ i ∈ Icc 1 n', a i) / α + ↑(∑ i ∈ Icc (k - l + 1) k, a i) / α := by rel [ih, hlt]
        _ ≤ (∑ i ∈ Icc 1 n, a i) / α := by
          -- applying ih, it suffices to prove (∑ i ∈ Icc 1 n', a i) / α + (∑ i ∈ Icc (k - l + 1) k, a i) / α ≤ (∑ i ∈ Icc 1 n, a i) / α
          field_simp
          have : Icc 1 n = Icc 1 n' ∪ Icc (k - l + 1) n := by
            ext i
            simp
            constructor <;> intro h
            · by_cases hle : i ≤ n'
              · apply Or.inl
                simp at h hle ⊢
                exact ⟨h.1, hle⟩
              · simp at hle
                apply Or.inr
                simp at h hle ⊢
                exact ⟨hle, h.right⟩
            · rcases h with h | h
              · exact ⟨h.1, le_trans h.2 hnn'⟩
              · constructor
                · calc
                    1 ≤ k - l + 1 := by exact Nat.le_add_left 1 (k - l)
                    _ ≤ i := by exact h.left
                · exact h.right
          rw [this]
          have : Disjoint (Icc 1 n') (Icc (k - l + 1) n) := by
            intro i hi hi' x hx
            have : x ≤ n' := by apply hi at hx; simp at hx; exact hx.2
            have : ¬ x ≤ n' := by
              simp
              apply hi' at hx
              simp at hx
              exact hx.left
            contradiction
          rw [Finset.sum_union this]
          apply (div_le_div_iff_of_pos_right hα).mpr
          simp
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i
            simp
            intro hi1 hi2
            exact ⟨hi1, le_trans hi2 hk.2⟩
          · intro i hi _
            apply le_of_lt
            norm_cast
            apply ha
            simp at hi ⊢
            constructor
            · calc
                1 ≤ k - l + 1 := by exact Nat.le_add_left 1 (k - l)
                _ ≤ i := by exact hi.left
            · exact hi.right
  · -- if S is empty, then the statement is trivial
    simp at hS
    simp [hS]
    apply div_pos ?_ hα
    apply Finset.sum_pos
    · norm_cast
    · simp; exact hn
