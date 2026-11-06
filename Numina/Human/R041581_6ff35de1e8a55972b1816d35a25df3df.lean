import Mathlib

open Real Set
open scoped BigOperators

/- Given a sequence $a_{1}, a_{2}, \ldots, a_{n}$ of real numbers. For each $i(1 \leq i \leq n)$ define  $$ d_{i}=\max \left\{a_{j}: 1 \leq j \leq i\right\}-\min \left\{a_{j}: i \leq j \leq n\right\} $$  and let  $$ d=\max \left\{d_{i}: 1 \leq i \leq n\right\} $$  (a) Prove that for arbitrary real numbers $x_{1} \leq x_{2} \leq \ldots \leq x_{n}$,  $$ \max \left\{\left|x_{i}-a_{i}\right|: 1 \leq i \leq n\right\} \geq \frac{d}{2} $$  (b) Show that there exists a sequence $x_{1} \leq x_{2} \leq \ldots \leq x_{n}$ of real numbers such that we have equality in (1).  (New Zealand) -/
theorem inequalities_23620 {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (d : ℕ → ℝ) (d₀ : ℝ)
    (h₀ : ∀ i ∈ Finset.Icc 1 n, d i = sSup ((Finset.Icc 1 i).image a) - sInf ((Finset.Icc i n).image a))
    (h₁ : IsGreatest {d i | i ∈ Finset.Icc 1 n} d₀) :
    (∀ x : ℕ → ℝ, MonotoneOn x (Finset.Icc 1 n) → sSup ((Finset.Icc 1 n).image (fun i ↦ abs (x i - a i))) ≥ d₀ / 2) ∧
    ∃ x : ℕ → ℝ, MonotoneOn x (Finset.Icc 1 n) ∧ sSup ((Finset.Icc 1 n).image (fun i ↦ abs (x i - a i))) = d₀ / 2 := by
  -- (a) Let $1 \leq p \leq q \leq r \leq n$ be indices for which
  -- $$ d=d_{q},
  obtain ⟨q, hqmem, hqeq⟩ : ∃ q ∈ Finset.Icc 1 n, d q = d₀ := by
    simp only [IsGreatest] at h₁
    exact h₁.left
  have hqge1 : q ≥ 1 := by simp at hqmem; exact hqmem.1
  have hqlen : q ≤ n := by simp at hqmem; exact hqmem.2
  -- \quad a_{p}=\max \left\{a_{j}: 1 \leq j \leq q\right\},
  obtain ⟨p, hpmem, hpeq⟩ : ∃ p ∈ Finset.Icc 1 q, a p = sSup ((Finset.Icc 1 q).image a) := by
    have : ((Finset.Icc 1 q).image a).Nonempty := by use a 1; simp; use 1
    apply Finset.Nonempty.csSup_mem at this
    apply Finset.mem_image.mp at this
    obtain ⟨p, hp, hp_eq⟩ := this
    use p
  have hpge1 : p ≥ 1 := by simp at hpmem; exact hpmem.1
  have hpleq : p ≤ q := by simp at hpmem; exact hpmem.2
  have hpmem' : p ∈ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    exact ⟨hpge1, le_trans hpleq hqlen⟩
  -- \quad a_{r}=\min \left\{a_{j}: q \leq j \leq n\right\} $$
  obtain ⟨r, hrmem, hreq⟩ : ∃ r ∈ Finset.Icc q n, a r = sInf ((Finset.Icc q n).image a) := by
    have : ((Finset.Icc q n).image a).Nonempty := by use a q; apply Finset.mem_image.mpr; use q; simp only [Finset.mem_Icc, le_refl, true_and, and_true, hqlen]
    apply Finset.Nonempty.csInf_mem at this
    apply Finset.mem_image.mp at this
    obtain ⟨r, hr, hr_eq⟩ := this
    use r
  have hrgeq : r ≥ q := by simp at hrmem; exact hrmem.1
  have hrlen : r ≤ n := by simp at hrmem; exact hrmem.2
  have hrmem' : r ∈ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    exact ⟨le_trans hqge1 hrgeq, hrlen⟩
  -- and thus $d=a_{p}-a_{r}$.
  -- (These indices are not necessarily unique.)
  have hdeq : d₀ = a p - a r := by rw [hpeq, hreq, ←hqeq]; exact h₀ q hqmem

  have ssup_ge : ∀ x : ℕ → ℝ, MonotoneOn x (Finset.Icc 1 n) → sSup ((Finset.Icc 1 n).image (fun i ↦ abs (x i - a i))) ≥ d₀ / 2 := by
    -- For arbitrary real numbers $x_{1} \leq x_{2} \leq \ldots \leq x_{n}$,
    intro x hmon
    -- consider just the two quantities $\left|x_{p}-a_{p}\right|$ and $\left|x_{r}-a_{r}\right|$.
    let d₁ : ℝ := abs (x p - a p)
    let d₂ : ℝ := abs (x r - a r)
    -- Since $$ \left(a_{p}-x_{p}\right)+\left(x_{r}-a_{r}\right)=\left(a_{p}-a_{r}\right)+\left(x_{r}-x_{p}\right) \geq a_{p}-a_{r}=d,
    have hsumge : d₁ + d₂ ≥ d₀ := by
      calc
        d₁ + d₂ ≥ a p - x p + (x r - a r) := by
          apply add_le_add
          · apply le_of_eq_of_le (b := -(x p - a p))
            · rw [neg_sub]
            · exact neg_le_abs (x p - a p)
          · exact le_abs_self (x r - a r)
        _ = a p - a r + (x r - x p) := by ring
        _ ≥ a p - a r := by
          apply le_add_iff_nonneg_right _|>.mpr
          apply sub_nonneg.mpr
          apply hmon
          · exact hpmem'
          · exact hrmem'
          · exact le_trans hpleq hrgeq
        _ = d₀ := by rw [hdeq]
    -- $$ we have either $a_{p}-x_{p} \geq \frac{d}{2}$ or $x_{r}-a_{r} \geq \frac{d}{2}$.
    have hmaxge : max d₁ d₂ ≥ d₀ / 2 := by
      by_contra h
      push_neg at h
      apply max_lt_iff.mp at h
      have : d₀ < d₀ := by
        calc
          d₀ ≤ d₁ + d₂ := by exact hsumge
          _ < d₀ / 2 + d₀ / 2 := by exact add_lt_add h.1 h.2
          _ = d₀ := by ring
      exact lt_self_iff_false _ |>.mp this
    -- Hence, $$ \max \left\{\left|x_{i}-a_{i}\right|: 1 \leq i \leq n\right\} \geq \max \left\{\left|x_{p}-a_{p}\right|,\left|x_{r}-a_{r}\right|\right\}
    -- \geq \max \left\{a_{p}-x_{p}, x_{r}-a_{r}\right\} \geq \frac{d}{2} $$
    apply le_trans hmaxge
    apply max_le
    · apply le_csSup
      · exact Finset.bddAbove (Finset.image (fun i ↦ |x i - a i|) (Finset.Icc 1 n))
      · apply Finset.mem_image.mpr
        use p, hpmem'
    · apply le_csSup
      · exact Finset.bddAbove (Finset.image (fun i ↦ |x i - a i|) (Finset.Icc 1 n))
      · apply Finset.mem_image.mpr
        use r, hrmem'

  constructor
  · exact ssup_ge
  · -- (b) Define the sequence $\left(x_{k}\right)$ as
    -- $$ x_{1}=a_{1}-\frac{d}{2}, \quad x_{k}=\max \left\{x_{k-1}, a_{k}-\frac{d}{2}\right\} \quad \text { for } 2 \leq k \leq n $$
    let x (i : ℕ) : ℝ := sSup ((Finset.Icc 1 i).image (fun j ↦ a j - d₀ / 2))
    -- We show that we have equality in (1) for this sequence.
    use x
    have hmon : MonotoneOn x (Finset.Icc 1 n) := by
      -- By the definition, sequence $\left(x_{k}\right)$ is non-decreasing
      intro c hc b _ hle
      unfold x
      apply csSup_le_csSup
      · apply Finset.bddAbove
      · use a c - d₀ / 2
        apply Finset.mem_image.mpr
        use c
        constructor
        · apply Finset.right_mem_Icc.mpr
          simp only [Finset.coe_Icc, Set.mem_Icc] at hc
          exact hc.1
        · rfl
      · simp only [Finset.coe_image, Finset.coe_Icc]
        intro x hx
        obtain ⟨y, hy1, hy2⟩ := hx
        use y
        constructor
        · simp at hy1 ⊢
          exact ⟨hy1.1, le_trans hy1.2 hle⟩
        · exact hy2
    have hx {i : ℕ} (hi : i ≥ 2) : x i = max (x (i - 1)) (a i - d₀ / 2) := by
      apply le_antisymm
      · apply csSup_le
        · use a 1 - d₀ / 2
          simp
          use 1
          simp
          exact Nat.one_le_of_lt hi
        · intro b hb
          simp at hb
          obtain ⟨k, hk, hb⟩ := hb
          by_cases hk' : k ≤ i - 1
          · have : b ≤ x (i - 1) := by
              apply le_csSup
              · apply Finset.bddAbove
              · simp
                use k
                simp [hb, hk.1, hk']
            exact le_max_of_le_left this
          · have : k = i := by
              apply le_antisymm hk.2
              simp at hk'
              exact Nat.le_of_pred_lt hk'
            simp [←hb, this]
      · simp only [sup_le_iff]
        constructor
        · apply csSup_le_csSup
          · apply Finset.bddAbove
          · use a (i - 1) - d₀ / 2
            simp
            use i - 1
            simp
            exact Nat.le_sub_one_of_lt hi
          · norm_cast
            apply Finset.image_subset_image
            intro x hx
            simp at hx ⊢
            obtain ⟨h₁, h₂⟩ := hx
            use h₁
            apply le_trans h₂
            simp
        · apply le_csSup
          · apply Finset.bddAbove
          · simp
            use i
            simp
            exact Nat.one_le_of_lt hi
    use hmon
    apply le_antisymm ?_ (ssup_ge x hmon)
    apply csSup_le
    · use |x 1 - a 1|
      apply Finset.mem_image.mpr
      use 1
      constructor
      · apply Finset.left_mem_Icc.mpr
        exact hn
      · rfl
    · intro r hr
      apply Finset.mem_image.mp at hr
      obtain ⟨k, hk, hkr⟩ := hr
      rw [←hkr]
      apply abs_le.mpr
      constructor
      · -- and $x_{k}-a_{k} \geq-\frac{d}{2}$ for all $1 \leq k \leq n$.
        calc
          _ = a k - d₀ / 2 - a k := by ring_nf
          _ ≤ _ := by
            apply sub_le_sub_right
            unfold x
            apply le_csSup
            · apply Finset.bddAbove
            · apply Finset.mem_image.mpr
              use k
              constructor
              · apply Finset.right_mem_Icc.mpr
                simp at hk
                exact hk.1
              · rfl
      · -- Next we prove that $$ x_{k}-a_{k} \leq \frac{d}{2} \quad \text { for all } 1 \leq k \leq n $$
        -- Consider an arbitrary index $1 \leq k \leq n$.
        -- Let $\ell \leq k$ be the smallest index such that $x_{k}=x_{\ell}$.
        have hne : ((Finset.Icc 1 k).filter (fun i => x i = x k)).Nonempty := by
          use k
          refine Finset.mem_filter.mpr ?h.a
          constructor
          · refine Finset.right_mem_Icc.mpr ?h.a.left.a
            simp at hk
            exact hk.1
          · rfl
        let ℓ : ℕ := ((Finset.Icc 1 k).filter (fun i => x i = x k)).min' hne
        have hℓmem : ℓ ∈ ((Finset.Icc 1 k).filter (fun i => x i = x k)) := by
          apply Finset.min'_mem at hne
          exact hne
        have hℓmem' : ℓ ∈ Finset.Icc 1 k := by
          apply Finset.mem_filter.mp at hℓmem
          exact hℓmem.1
        -- We have either $\ell=1$, or $\ell \geq 2$ and $x_{\ell}&gt;x_{\ell-1}$.
        have hℓ : ℓ = 1 ∨ ℓ ≥ 2 ∧ x ℓ > x (ℓ - 1) := by
          by_cases h : ℓ = 1
          · simp [h]
          · simp [h]
            have h : ℓ ≥ 2 := by
              apply lt_or_gt_of_ne at h
              have : ¬ ℓ < 1 := by push_neg; simp at hℓmem'; exact hℓmem'.1
              simp [this] at h
              exact h
            constructor
            · exact h
            · by_contra h'
              simp at h'
              have : x ℓ = x (ℓ - 1) := by
                apply le_antisymm h'
                apply csSup_le_csSup
                · apply Finset.bddAbove
                · use a 1 - d₀ / 2
                  simp
                  use 1
                  simp
                  exact Nat.le_sub_one_of_lt h
                · norm_cast
                  apply Finset.image_subset_image
                  intro x hx
                  simp at hx ⊢
                  use hx.1
                  apply le_trans hx.2
                  simp
              have : ℓ ≤ ℓ - 1 := by
                apply Finset.min'_le
                simp at hℓmem
                simp [←this, ←hℓmem.2]
                constructor
                · exact Nat.le_sub_one_of_lt h
                · apply le_trans hℓmem.1.2
                  simp
              have : ¬ ℓ ≤ ℓ - 1 := by simp; exact Nat.zero_lt_of_lt h
              contradiction
        -- In both cases, $$ x_{k}=x_{\ell}=a_{\ell}-\frac{d}{2} $$
        have hℓ' : x k = a ℓ - d₀ / 2 := by
          apply Finset.min'_mem at hne
          apply Finset.mem_filter.mp at hne
          rw [←hne.2]
          change x ℓ = a ℓ - d₀ / 2
          apply le_antisymm
          · rcases hℓ with h | h
            · simp [h, x]
            · obtain hx := hx h.1
              simp [hx] at h
              simp [hx]
              apply le_sub_right_of_add_le
              exact le_of_lt h.2
          · apply le_csSup
            · apply Finset.bddAbove
            · apply Finset.mem_image.mpr
              use ℓ
              constructor
              · simp
                simp at hℓmem'
                exact hℓmem'.1
              · rfl
        -- Since $$ a_{\ell}-a_{k} \leq \max \left\{a_{j}: 1 \leq j \leq k\right\}-\min \left\{a_{j}: k \leq j \leq n\right\}=d_{k} \leq d $$
        have : a ℓ- a k ≤ d₀ := by
          calc
            a ℓ - a k ≤ sSup ((Finset.Icc 1 k).image a) - sInf ((Finset.Icc k n).image a) := by
              apply sub_le_sub
              · apply le_csSup
                · exact Finset.bddAbove (Finset.image a (Finset.Icc 1 k))
                · apply Finset.mem_image.mpr
                  use ℓ
              · apply csInf_le
                · exact Finset.bddBelow (Finset.image a (Finset.Icc k n))
                · apply Finset.mem_image.mpr
                  use k
                  constructor
                  · simp
                    simp at hk
                    exact hk.2
                  · rfl
            _ = d k := by rw [h₀]; exact hk
            _ ≤ d₀ := by
              simp only [IsGreatest] at h₁
              obtain h₁ := h₁.2
              apply Set.mem_setOf.mp at h₁
              apply h₁
              apply Set.mem_setOf.mpr
              use k
        -- equality (3) implies $$ x_{k}-a_{k}=a_{\ell}-a_{k}-\frac{d}{2} \leq d-\frac{d}{2}=\frac{d}{2} $$
        calc
          x k - a k = a ℓ - a k - d₀ / 2 := by rw [hℓ']; ring
          _ ≤ d₀ - d₀ / 2 := by rel [this]
          _ = d₀ / 2 := by ring
      -- We obtained that $-\frac{d}{2} \leq x_{k}-a_{k} \leq \frac{d}{2}$ for all $1 \leq k \leq n$,
      -- so $$ \max \left\{\left|x_{i}-a_{i}\right|: 1 \leq i \leq n\right\} \leq \frac{d}{2} $$
      -- We have equality because $\left|x_{1}-a_{1}\right|=\frac{d}{2}$.
