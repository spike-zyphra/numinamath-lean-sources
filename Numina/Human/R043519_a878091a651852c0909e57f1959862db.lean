import Mathlib

/-
  Find the largest real number $c$ such that

$$
\sum_{i=1}^{101} x_{i}^{2} \geq c M^{2}
$$

whenever $x_{1}, \ldots, x_{101}$ are real numbers such that $x_{1}+\cdots+x_{101}=0$ and $M$ is the median of $x_{1}, \ldots, x_{101}$.
-/
theorem inequalities_609217 {median : (Fin 101 → ℝ) → ℝ}
    {hmedian : ∀ f, median f = ((List.ofFn f).insertionSort LE.le)[50]'(by rw [List.length_insertionSort, List.length_ofFn]; simp)} :
    IsGreatest {c : ℝ | ∀ x : Fin 101 → ℝ, ∑ i, x i = 0 → ∑ i, x i ^ 2 ≥ c * (median x) ^ 2} (5151 / 50) := by
  constructor
  · simp
    intro x hsum
    --  Suppose without loss of generality that $x_{1} \leq \cdots \leq x_{101}$.
    wlog hsord : Monotone x generalizing x with H
    · -- otherwise, we sort the list
      let x' (i : Fin 101) := (List.ofFn x).insertionSort LE.le |>.get ⟨i.1, by rw [List.length_insertionSort, List.length_ofFn]; simp⟩
      obtain hperm : ((List.ofFn x).insertionSort LE.le).Perm (List.ofFn x) := by exact List.perm_insertionSort LE.le (List.ofFn x)
      -- note that the sorted list is a permutation of the original list
      have bijection_of_perm {l₁ l₂ : List ℝ} (h : l₁.Perm l₂) :
          ∃ f : Fin l₁.length → Fin l₂.length, Function.Bijective f ∧ ∀ i, l₁.get i = l₂.get (f i) := by
        induction h with
        | nil => simp
        | cons x hp ih =>
          rename_i l₁' l₂'
          obtain ⟨f, hbi, hf⟩ := ih
          let f' (i : Fin (x :: l₁').length) : Fin (x :: l₂').length :=
            if h : i.1 = 0 then ⟨0, by simp⟩
            else ⟨f ⟨i.1 - 1, by
              apply lt_of_lt_of_le (b := (x :: l₁').length - 1)
              · refine Nat.sub_lt_sub_right ?_ ?_
                · exact Nat.one_le_iff_ne_zero.mpr h
                · exact i.isLt
              · simp
            ⟩ + 1, by simp⟩
          use f'
          constructor
          · apply Fintype.bijective_iff_injective_and_card _ |>.mpr
            simp [f']
            constructor
            · intro ⟨x, hx⟩ ⟨y, hy⟩ hf
              apply Fin.ext_iff.mp at hf
              by_cases h : x = 0
              · simp [h] at hf
                by_cases h' : y = 0
                · simp [h, h']
                · simp [h'] at hf
              · by_cases h' : y = 0
                · simp [h, h'] at hf
                · simp [h, h'] at hf
                  apply Fin.ext_iff.mpr at hf
                  apply hbi.1 at hf
                  apply Fin.ext_iff.mp at hf
                  simp at hf ⊢
                  apply tsub_left_inj ?_ ?_ |>.mp hf
                  · exact Nat.one_le_iff_ne_zero.mpr h
                  · exact Nat.one_le_iff_ne_zero.mpr h'
            · exact List.Perm.length_eq hp
          · intro ⟨i, hi⟩
            simp [f']
            by_cases h : i = 0
            · simp [h]
            · simp [h]
              simp at hf
              rw [←hf, List.getElem_cons]
              simp [h]
        | swap x₁ x₂ l =>
          let f (x : Fin (x₁ :: x₂ :: l).length) : Fin (x₂ :: x₁ :: l).length :=
            if x.1 = 0 then ⟨1, by simp⟩
            else if x.1 = 1 then ⟨0, by simp⟩
            else x
          use f
          constructor
          · apply Fintype.bijective_iff_injective_and_card _ |>.mpr
            simp [f]
            intro ⟨x, hx⟩ ⟨y, hy⟩ hf
            apply Fin.ext_iff.mp at hf
            by_cases h : x = 0
            · simp [h] at hf
              by_cases h' : y = 0
              · simp [h, h']
              · simp [h'] at hf
                by_cases h : y = 1
                · simp [h] at hf
                · simp [h] at hf
                  simp [hf] at h
            · simp [h] at hf
              by_cases h' : y = 0
              · simp [h'] at hf
                by_cases h : x = 1
                · simp [h] at hf
                · simp [h] at hf
              · simp [h'] at hf
                by_cases hx : x = 1
                · simp [hx] at hf
                  by_cases hy : y = 1
                  · simp [hy, hx]
                  · simp [hy] at hf
                    simp [hf] at h'
                · simp [hx] at hf
                  by_cases hy : y = 1
                  · simp [hy] at hf
                    simp [hf] at h
                  · simp [hy] at hf
                    exact Fin.mk.inj_iff.mpr hf
          · intro ⟨i, hi⟩
            simp [f]
            by_cases h : i = 0
            · simp [h]
            · by_cases h' : i = 1
              · simp [h']
              · simp [h, h']
                rw [List.getElem_cons, List.getElem_cons]
                simp [h, h']
                rw [List.getElem_cons, List.getElem_cons]
                have : i - 1 ≠ 0 := by
                  intro h''
                  have : i ≤ 1 := by exact Nat.le_of_sub_eq_zero h''
                  interval_cases i
                  all_goals simp at h h'
                simp [this]
        | trans _ _ ih₁ ih₂ =>
          rename_i l₁ _ _
          obtain ⟨f₁, hf₁⟩ := ih₁
          obtain ⟨f₂, hf₂⟩ := ih₂
          use f₂ ∘ f₁
          constructor
          · refine Function.Bijective.comp hf₂.1 hf₁.1
          · intro i
            rw [hf₁.2, hf₂.2]
            congr
      obtain ⟨f, hb, hf⟩ := bijection_of_perm hperm
      have hsum' : ∑ i, x' i = 0 := by
        unfold x'
        trans  ∑ i : Fin 101, (List.ofFn x).get (f ⟨i, by rw [List.length_insertionSort, List.length_ofFn]; simp⟩)
        · apply Finset.sum_congr rfl
          intro i _
          rw [hf]
        . have : Finset.univ.image (fun i : Fin 101 => f ⟨i, by rw [List.length_insertionSort, List.length_ofFn]; simp⟩) = Finset.univ := by
            apply Finset.image_univ_of_surjective
            intro y
            obtain ⟨x, hx⟩ := hb.2 y
            use ⟨x.1, by apply lt_of_lt_of_eq x.2; rw [List.length_insertionSort, List.length_ofFn]⟩
          rw [←Finset.sum_image, this]
          · rw [←Fin.sum_ofFn, List.ofFn_get]
            rw [Fin.sum_ofFn]
            exact hsum
          · intro x _ y _ hf
            apply hb.1 at hf
            apply Fin.val_eq_of_eq at hf
            simp at hf
            exact Fin.eq_of_val_eq hf
      have hmono : Monotone x' := by
        intro x y hle
        apply List.Sorted.rel_get_of_le (List.sorted_insertionSort LE.le (List.ofFn _)) hle
      have hmedian' : median x' = median x := by
        rw [hmedian, hmedian]
        apply List.getElem_of_eq
        have : List.Sorted LE.le (List.ofFn x') := by exact Monotone.ofFn_sorted hmono
        rw [List.Sorted.insertionSort_eq this]
        apply List.ext_get
        · unfold x'
          rw [List.length_ofFn, List.length_insertionSort, List.length_ofFn]
        · intro _ _ _
          rw [List.get_ofFn]
          unfold x'
          rfl
      have hsqsum : ∑ i, (x' i) ^ 2 = ∑ i, (x i) ^ 2 := by
        unfold x'
        trans  ∑ i : Fin 101, (x (f ⟨i, by rw [List.length_insertionSort, List.length_ofFn]; simp⟩)) ^ 2
        · apply Finset.sum_congr rfl
          intro i _
          rw [hf]
          rw [List.get_ofFn]
          congr
        · have : Finset.univ = Finset.univ.image (fun i : Fin 101 => (f ⟨i.1, by rw [List.length_insertionSort, List.length_ofFn]; simp⟩ : Fin 101)) := by
            symm
            apply Finset.image_univ_of_surjective
            intro y
            obtain ⟨x, hx⟩ := hb.2 y
            use ⟨x.1, by apply lt_of_lt_of_eq x.2; rw [List.length_insertionSort, List.length_ofFn]⟩
          nth_rw 2 [this]
          rw [Finset.sum_image]
          intro x _ y _ hf
          apply hb.1 at hf
          ext
          apply Fin.val_eq_of_eq hf
      apply H x' hsum' at hmono
      rw [hmedian', hsqsum] at hmono
      exact hmono
    · -- Indeed, we may set $u=x_{51}-\left(x_{1}+\cdots+x_{50}\right) / 50$ and $v=\left(x_{52}+\cdots+x_{101}\right) / 50-x_{51}$,
      let u := ∑ i : Fin 50, x i
      let v := ∑ i : Fin 50, x ⟨i.val + 51, by apply lt_of_lt_of_eq (b := 50 + 51); apply add_lt_add_right i.2; simp⟩
      let u' := ∑ i : Fin 50, x i ^ 2
      let v' := ∑ i : Fin 50, x ⟨i.val + 51, by apply lt_of_lt_of_eq (b := 50 + 51); apply add_lt_add_right i.2; simp⟩ ^ 2
      have hcup : Finset.univ = Finset.univ.filter (fun i : Fin 101 => i.val < 50) ∪ {⟨50, by simp⟩} ∪ Finset.univ.filter (fun i : Fin 101 => i.val ≥ 51) := by
        ext ⟨i, hi⟩
        simp
        by_cases h : i < 50
        · simp [h]
        · simp at h
          rcases lt_or_eq_of_le h with h | h
          · right; right
            exact h
          · simp [←h]
      have hdis₁ : Disjoint (Finset.filter (fun i : Fin 101 ↦ i.val < 50) Finset.univ) {⟨50, by simp⟩} := by simp; rfl
      have hdis₂ : Disjoint (Finset.filter (fun i : Fin 101 ↦ i.val < 50) Finset.univ ∪ {⟨50, by simp⟩}) (Finset.filter (fun i : Fin 101 ↦ ↑i.val ≥ 51) Finset.univ) := by
        intro a hsub1 hsub2 c hcmem
        obtain h₁ := hsub1 hcmem
        obtain h₂ := hsub2 hcmem
        simp at h₁ h₂
        rcases h₁ with h | h
        · linarith
        · simp [h] at h₂
          apply Fin.mk_le_of_le_val at h₂
          simp at h₂
      -- prove u + x_{51} + v = 0 and u' + x_{51}^{2} + v' = ∑ i=1^{101} x_{i}^{2}
      have hsum₁ : ∑ i : Fin 101, x i = u + x ⟨50, by simp⟩ + v := by
        unfold u v
        rw [hcup, Finset.sum_union hdis₂, Finset.sum_union hdis₁]
        simp
        congr 1
      have hsum₂ : ∑ i : Fin 101, x i ^ 2 = u' + x ⟨50, by simp⟩ ^ 2 + v' := by
        unfold u' v'
        rw [hcup, Finset.sum_union hdis₂, Finset.sum_union hdis₁]
        simp
        congr 1
      -- the median of $x_{1},\ldots,x_{101}$ is $x_{51}$, so we have
      have hmedian : median x = x ⟨50, by simp⟩ := by
        rw [hmedian]
        have : x ⟨50, by simp⟩ = (List.ofFn x)[50]'(by rw [List.length_ofFn]; simp) := by rw [List.getElem_ofFn]
        rw [this]
        apply List.getElem_of_eq
        apply List.Sorted.insertionSort_eq
        exact Monotone.ofFn_sorted hsord
      trans u ^ 2 / 50 + x ⟨50, by simp⟩ ^ 2 + v ^ 2 / 50
      · -- To prove u^2 + v^2 / 50 + x_{51}^{2} / 50 ≥ 5151 / 50 * x_{51}^{2}
        -- We note that u = - x_{51} - v
        -- eliminate u from the inequality
        apply le_of_mul_le_mul_left (a := 50)
        · ring_nf
          rw [hmedian]
          have hu : u = - x ⟨50, by simp⟩ - v := by
            trans 0 - x ⟨50, by simp⟩ - v
            · rw [←hsum, hsum₁]
              ring
            · ring
          rw [hu]
          apply sub_nonneg.mp
          ring_nf
          suffices h : 2 * (50 * x ⟨50, by simp⟩ - u) * (v - 50 * x ⟨50, by simp⟩) ≥ 0
          · -- then we still need to show that
            -- v ^ 2 - 2550 * x_{51}* v + x_{51}^{2} ≥ 0
            -- which is equivalent to
            -- (50 * x_{51} - v) * (v - 50 * x_{51}) ≥ 0
            apply le_of_le_of_eq h
            rw [hu]
            ring
          · -- note that x is sorted, so we have
            -- 50 * x_{51} - v ≥ 0
            -- and v - 50 * x_{51} ≥ 0
            apply mul_nonneg
            · simp
              unfold u
              trans (Finset.univ (α := Fin 50)).card • x ⟨50, by simp⟩
              · rw [←Finset.sum_const]
                apply Finset.sum_le_sum
                intro _ _
                apply hsord
                simp
                apply Nat.le_of_lt_succ
                simp
                rw [Nat.mod_eq_of_lt]
                · apply lt_trans (Fin.isLt _)
                  exact lt_add_one 50
                · apply lt_trans (Fin.isLt _)
                  simp
              · simp
            · simp
              unfold v
              trans (Finset.univ (α := Fin 50)).card • x ⟨50, by simp⟩
              · simp
              · rw [←Finset.sum_const]
                apply Finset.sum_le_sum
                intro _ _
                apply hsord
                simp
                apply Nat.le_of_lt_succ
                simp
                rw [Nat.add_assoc]
                apply Nat.lt_add_left
                norm_cast
        · simp
      · -- One may also use the Cauchy-Schwarz inequality or the QM-AM inequality instead of Jensen's inequality.
        rw [hsum₂]
        apply add_le_add
        · apply add_le_add
          · apply div_le_iff₀ ?_ |>.mpr
            · rw [mul_comm]
              unfold u u'
              rw [show (50 : ℝ) = (Finset.univ (α := Fin 50)).card by simp]
              exact sq_sum_le_card_mul_sum_sq
            · simp
          · rfl
        · apply div_le_iff₀ ?_ |>.mpr
          · rw [mul_comm]
            unfold v v'
            rw [show (50 : ℝ) = (Finset.univ (α := Fin 50)).card by simp]
            exact sq_sum_le_card_mul_sum_sq
          · simp
  · intro c hc
    simp at hc
    -- The upperbound is witnessed by $x_{1}=\cdots=$ $x_{50}=-51 r$ and $x_{51}=\cdots=x_{101}=50 r$ for some r > 0
    let f := fun i : Fin 101 => if i < 50 then -51 else (50 : ℝ)
    have h₁ : (Finset.filter (fun x : Fin 101 ↦ x < 50) Finset.univ).card = 50 := rfl
    have h₂ : (Finset.filter (fun x : Fin 101 ↦ x ≥ 50) Finset.univ).card = 51 := rfl
    have hsum : ∑ i, f i = 0 := by
      simp [f]
      rw [Finset.sum_ite]
      simp [h₁, h₂]
      ring_nf
    apply hc f at hsum
    have hm : median (fun i ↦ if i < 50 then -51 else 50) = 50 := by
      have : (List.ofFn fun i : Fin 101 ↦ if i < 50 then -51 else (50 : ℝ))[50]'(by rw [List.length_ofFn]; simp) = (50 : ℝ) := by
        rw [List.getElem_ofFn]
        simp
      nth_rewrite 2 [←this]
      rw [hmedian]
      congr
      rw [List.Sorted.insertionSort_eq]
      apply List.pairwise_ofFn.mpr
      intro i j hlt
      by_cases hi : i < 50
      · by_cases hj : j < 50
        · simp [hi, hj]
        · simp [hi, hj]
          norm_num
      · simp [hi]
        have : ¬ j < 50 := by simp at hi ⊢; apply le_trans hi (le_of_lt hlt)
        simp [this]
    rw [hm] at hsum
    unfold f at hsum
    simp [ite_pow, Finset.sum_ite, h₁, h₂] at hsum
    norm_num at hsum
    linarith only [hsum]
