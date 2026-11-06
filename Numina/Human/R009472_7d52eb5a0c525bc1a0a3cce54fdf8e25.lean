import Mathlib

open Finset Real

/- Let $a_{1}, a_{2}, a_{3}, \ldots, a_{n}$ be a sequence of non-negative integers, where $n$ is a positive integer.
Let
$$
A_{n}=\frac{a_{1}+a_{2}+\cdots+a_{n}}{n}
$$
Prove that
$$
a_{1}!a_{2}!\ldots a_{n}!\geq\left(\left\lfloor A_{n}\right\rfloor!\right)^{n}
$$
where $\left\lfloor A_{n}\right\rfloor$ is the greatest integer less than or equal to $A_{n}$, and $a!=1 \times 2 \times \cdots \times a$ for $a \geq 1$ (and $0!=1$ ). When does equality hold? -/
theorem inequalities_607114 {n : ℕ} (hn : 0 < n) (a : Fin n → ℕ)
    (A : ℝ) (hA : A = (∑ i, a i) / n) :
    ∏ i, (a i).factorial ≥ (Nat.factorial ⌊A⌋₊) ^ n ∧
    (∏ i, (a i).factorial = (Nat.factorial ⌊A⌋₊) ^ n ↔ (∀ i, a i ≤ 1) ∨ (∃ b, ∀ i, a i = b)) := by
  have hAnonneg : A ≥ 0 := by
    rw [hA, Nat.cast_sum]
    apply div_nonneg
    · apply sum_nonneg
      intro _ _
      apply Nat.cast_nonneg
    · apply Nat.cast_nonneg
  -- Assume without loss of generality that $a_{1} \geq a_{2} \geq \cdots \geq a_{n} \geq 0$
  wlog hmono : Antitone a generalizing a with H
  · let a' (x : Fin n) := ((List.ofFn a).insertionSort (fun r₁ r₂ => r₁ ≥ r₂)).get ⟨x, by simp⟩
    have hsorted : ((List.ofFn a).insertionSort (fun r₁ r₂ => r₁ ≥ r₂)).Sorted (fun r₁ r₂ => r₁ ≥ r₂) := by
      exact List.sorted_insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) (List.ofFn a)
    have hmono : Antitone a' := by
      intro i j hij
      simp [a']
      exact List.Sorted.rel_get_of_le hsorted hij
    obtain hperm := List.perm_insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) (List.ofFn a)
    have bijection_of_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
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
    have huniv : univ = image (fun i : Fin n ↦ @Fin.cast (List.ofFn a).length n (by simp) (f ⟨↑i, by simp⟩)) univ := by
      symm
      apply Finset.image_univ_of_surjective
      intro y
      obtain ⟨a, ha⟩ := hb.2 ⟨y, by simp⟩
      use ⟨a, by apply lt_of_lt_of_eq a.2; simp⟩
      simp [ha]
    have hA : A = ↑(∑ i : Fin n, a' i) / (n : ℝ) := by
      rw [hA]
      congr 1
      norm_cast
      unfold a'
      simp only [hf, List.get_ofFn]
      nth_rw 1 1 [huniv, sum_image (g := fun i : Fin n => (@Fin.cast (List.ofFn a).length n (by simp) (f ⟨↑i, by simp⟩)))]
      intro _ _ _ _ hf
      apply Fin.cast_injective at hf
      apply hb.1 at hf
      apply Fin.eq_of_val_eq
      apply Fin.val_eq_of_eq at hf
      exact hf
    obtain ⟨hle, heq⟩ := H a' hA hmono
    have hprod : ∏ i : Fin n, (a' i).factorial = ∏ i : Fin n, (a i).factorial := by
      unfold a'
      simp only [hf, List.get_ofFn]
      nth_rw 2 [huniv]
      rw [prod_image]
      intro _ _ _ _ hf
      apply Fin.cast_injective at hf
      apply hb.1 at hf
      apply Fin.eq_of_val_eq
      apply Fin.val_eq_of_eq at hf
      exact hf
    rw [←hprod]
    use hle
    apply Iff.trans heq
    unfold a'
    simp only [hf, List.get_ofFn]
    have {i : Fin n} : a (@Fin.cast (List.ofFn a).length n (by simp) ⟨i, by simp⟩) = a i := by
      congr 1
    obtain ⟨g, _, hg2⟩ := Function.bijective_iff_has_inverse.mp hb
    constructor <;> intro h
    · rcases h with h | h
      · left
        intro i
        obtain h := h ⟨g ⟨i, by simp⟩, by apply lt_of_lt_of_le (Fin.isLt _); simp⟩
        apply le_trans ?_ h
        apply le_of_eq
        congr 1
        simp
        rw [hg2]
        rfl
      · right
        obtain ⟨b, hb⟩ := h
        use b
        intro i
        obtain h := hb ⟨g ⟨i, by simp⟩, by apply lt_of_lt_of_le (Fin.isLt _); simp⟩
        rw [←h]
        congr 1
        simp
        rw [hg2]
        rfl
    · rcases h with h | h
      · left
        intro i
        apply h
      · right
        obtain ⟨b, hb⟩ := h
        use b
        intro i
        apply hb
  · -- let $s=\left\lfloor A_{n}\right\rfloor$.
    let s := ⌊A⌋₊
    -- Let $k$ be any (fixed) index for which $a_{k} \geq s \geq a_{k+1}$.
    have hne : (univ.filter (fun i => a i ≥ s)).Nonempty := by
      use ⟨0, hn⟩
      apply mem_filter.mpr
      constructor
      · apply mem_univ
      · suffices h : a ⟨0, hn⟩ ≥ (s : ℝ)
        · apply Nat.cast_le.mp h
        · trans A
          · rw [hA]
            apply div_le_iff₀ ?_|>.mpr
            trans ∑ _ : Fin n, a ⟨0, hn⟩
            · rw [Nat.cast_sum]
              apply sum_le_sum
              intro i _
              apply Nat.cast_le.mpr
              apply hmono
              apply Fin.val_fin_le.mp
              apply Nat.zero_le
            · rw [sum_const, Finset.card_univ, Fintype.card_fin]
              simp only [nsmul_eq_mul, mul_comm]
              rfl
            · exact Nat.cast_pos'.mpr hn
          · unfold s
            apply Nat.floor_le hAnonneg
    let k := (Finset.univ.filter (fun i => a i ≥ s)).max' hne
    have hs_le : s ≤ a k := by
      obtain h := Finset.max'_mem _ hne
      apply Finset.mem_filter.mp at h
      exact h.2
    have hlt_of_gt_k {m : Fin n} (hm : m > k) : a m < s := by
      by_contra h
      push_neg at h
      apply Finset.max'_lt_iff _ hne |>.mp at hm
      obtain h := hm m (by apply mem_filter.mpr; exact ⟨mem_univ m, h⟩)
      apply lt_self_iff_false m |>.mp h
    have hunion : univ = Iic k ∪ Ioi k := by
      ext i
      simp only [mem_univ, mem_union, mem_Iic, mem_Ioi, true_iff]
      exact Fin.le_or_lt i k
    have hdis : Disjoint (Iic k) (Ioi k) := by
      refine disjoint_left.mpr ?_
      intro _ h
      simp only [mem_Iic] at h
      simp only [mem_Ioi, not_lt]
      exact h
    -- Our inequality is equivalent to proving that
    -- $$ \frac{a_{1}!}{s!} \cdot \frac{a_{2}!}{s!} \cdot \ldots \cdot \frac{a_{k}!}{s!} \geq \frac{s!}{a_{k+1}!} \cdot \frac{s!}{a_{k+2}!} \cdot \ldots \cdot \frac{s!}{a_{n}!} $$
    suffices h : ∏ i ∈ Iic k, (Nat.factorial (a i)) / (Nat.factorial s : ℝ) ≥ ∏ i ∈ Ioi k, (Nat.factorial s) / (Nat.factorial (a i) : ℝ) ∧
      (∏ i ∈ Iic k, (Nat.factorial (a i) : ℝ) / (Nat.factorial s) = ∏ i ∈ Ioi k, (Nat.factorial s) / (Nat.factorial (a i) : ℝ) ↔
      (∀ (i : Fin n), a i ≤ 1) ∨ ∃ b, ∀ (i : Fin n), a i = b)
    · simp only [prod_div_distrib] at h
      obtain ⟨hle , heq⟩ := h
      have h₁ : 0 < ∏ x ∈ Ioi k, ((a x).factorial : ℝ) := by
        apply prod_pos
        intro _ _
        apply Nat.cast_pos'.mpr
        apply Nat.factorial_pos
      have h₂ : 0 < ∏ _ ∈ Iic k, (s.factorial : ℝ) := by
        apply prod_pos
        intro _ _
        apply Nat.cast_pos'.mpr
        apply Nat.factorial_pos
      apply div_le_div_iff₀ h₁ h₂ |>.mp at hle
      norm_cast at hle
      constructor
      · trans (∏ i ∈ Iic k, (a i).factorial) * ∏ i ∈ Ioi k, (a i).factorial
        · nth_rw 1 [hunion, prod_union hdis]
        · apply le_trans ?_ hle
          rw [mul_comm, ←prod_union hdis, ←hunion, prod_const, Finset.card_univ, Fintype.card_fin]
      · apply Iff.trans ?_ heq
        apply Iff.trans ?_ (Iff.symm <| div_eq_div_iff ?_ ?_)
        · rw [←prod_union hdis, ←hunion, mul_comm, ←prod_union hdis, ←hunion]
          rw [prod_const, Finset.card_univ, Fintype.card_fin]
          norm_cast
        · apply ne_of_gt
          apply prod_pos
          intro i _
          apply Nat.cast_pos'.mpr
          exact Nat.factorial_pos s
        · apply ne_of_gt
          apply prod_pos
          intro i _
          apply Nat.cast_pos'.mpr
          exact Nat.factorial_pos (a i)
    · -- Now for $i=1,2, \ldots, k, a_{i}!/ s!$ is the product of $a_{i}-s$ factors.
      -- For example, 9!/5! $=9 \cdot 8 \cdot 7 \cdot 6$.
      have hdiv_ge {m n : ℕ} (hle : m ≥ n) : (m.factorial : ℝ) / (n.factorial : ℝ) ≥ (n + 1) ^ (m - n) := by
        apply le_div_iff₀ ?_ |>.mpr
        · norm_cast
          induction m, hle using Nat.le_induction
          · simp only [Nat.sub_self, pow_zero, one_mul, le_refl]
          · rename_i m hm ih
            rw [Nat.factorial_succ]
            trans (m + 1) * (n + 1) ^ (m - n) * n.factorial
            · apply Nat.mul_le_mul_right
              rw [Nat.sub_add_comm, Nat.pow_add_one']
              · apply Nat.mul_le_mul_right
                exact Nat.add_le_add_right hm 1
              · exact hm
            · rw [mul_assoc]
              apply Nat.mul_le_mul_left
              exact ih
        · apply Nat.cast_pos' |>.mpr
          apply Nat.factorial_pos
      have hdiv_lt_of_gt_succ {m n : ℕ} (h : m > n + 1) : (m.factorial : ℝ) / (n.factorial : ℝ) > (n + 1) ^ (m - n) := by
        apply lt_of_lt_of_le (b := ((m - 1 + 1).factorial : ℝ) / ((m - 1).factorial : ℝ) * (m - 1).factorial / (n.factorial : ℝ))
        · rw [Nat.factorial_succ, Nat.cast_mul, mul_div_cancel_right₀]
          · apply lt_of_eq_of_lt (b := (n + 1) * (↑n + 1 : ℝ) ^ (m - 1 - n))
            · norm_cast
              rw [←Nat.pow_add_one']
              congr
              rw [←Nat.sub_add_comm, Nat.sub_add_cancel]
              · exact Nat.one_le_of_lt h
              · apply Nat.le_sub_one_of_lt
                exact Nat.lt_of_succ_lt h
            · rw [mul_div_assoc]
              apply mul_lt_mul
              · norm_cast
                rw [Nat.sub_add_cancel]
                · exact h
                · exact Nat.one_le_of_lt h
              · apply hdiv_ge
                apply Nat.le_sub_one_of_lt
                exact Nat.lt_of_succ_lt h
              · apply pow_pos
                exact Nat.cast_add_one_pos n
              · apply Nat.cast_nonneg
          · apply ne_of_gt
            apply Nat.cast_pos'.mpr 
            apply Nat.factorial_pos
        · apply le_of_eq
          rw [div_mul_cancel₀]
          · rw[Nat.sub_add_cancel]
            exact Nat.one_le_of_lt h
          · apply ne_of_gt
            apply Nat.cast_pos'.mpr
            apply Nat.factorial_pos
      -- The left side of inequality (1) therefore is the product of $A=a_{1}+a_{2}+\cdots+a_{k}-k s$ factors,
      -- all of which are greater than $s$.
      have hLHS : ∏ i ∈ Iic k, ↑(a i).factorial / (s.factorial : ℝ) ≥ (s + 1) ^ (∑ i ∈ Iic k, a i - (k + 1) * s) := by
        trans (∏ i ∈ Iic k, (s + 1 : ℝ) ^ (a i - s))
        · apply prod_le_prod
          · intro _ _
            apply pow_nonneg
            apply add_nonneg
            · exact Nat.cast_nonneg' s
            · norm_num
          · intro _ h
            apply hdiv_ge
            apply Finset.mem_Iic.mp at h
            apply hmono at h
            exact Nat.le_trans hs_le h
        · rw [prod_pow_eq_pow_sum]
          apply pow_le_pow_right₀
          · apply le_add_of_nonneg_left
            exact Nat.cast_nonneg' s
          · apply Nat.cast_le (α := ℝ) |>.mp
            rw [Nat.cast_sub, Nat.cast_sum, Nat.cast_sum]
            · trans ∑ x ∈ Iic k, ((a x : ℝ) - s)
              · rw [sum_sub_distrib, sum_const, Nat.cast_mul, nsmul_eq_mul]
                apply le_of_eq
                congr
                exact Eq.symm (Fin.card_Iic k)
              · apply sum_le_sum
                intro i hi
                rw [Nat.cast_sub]
                apply mem_Iic.mp at hi
                apply hmono at hi
                exact Nat.le_trans hs_le hi
            · trans ∑ _ ∈ Iic k, s
              · rw [sum_const, nsmul_eq_mul]
                apply le_of_eq
                congr
                exact Eq.symm (Fin.card_Iic k)
              · apply sum_le_sum
                intro i hi
                apply mem_Iic.mp at hi
                apply hmono at hi
                exact Nat.le_trans hs_le hi
      have hLHS_gt_of (h : ∃ i ∈ Iic k, a i > s + 1) : ∏ i ∈ Iic k, ↑(a i).factorial / (s.factorial : ℝ) > (s + 1) ^ (∑ i ∈ Iic k, a i - (k + 1) * s) := by
        apply lt_of_le_of_lt (b := ∏ i ∈ Iic k, (s + 1 : ℝ) ^ (a i - s))
        · rw [prod_pow_eq_pow_sum]
          apply pow_le_pow_right₀
          · apply le_add_of_nonneg_left
            exact Nat.cast_nonneg' s
          · apply Nat.cast_le (α := ℝ) |>.mp
            rw [Nat.cast_sub, Nat.cast_sum, Nat.cast_sum]
            · trans ∑ x ∈ Iic k, ((a x : ℝ) - s)
              · rw [sum_sub_distrib, sum_const, Nat.cast_mul, nsmul_eq_mul]
                apply le_of_eq
                congr
                exact Eq.symm (Fin.card_Iic k)
              · apply sum_le_sum
                intro i hi
                rw [Nat.cast_sub]
                apply mem_Iic.mp at hi
                apply hmono at hi
                exact Nat.le_trans hs_le hi
            · trans ∑ _ ∈ Iic k, s
              · rw [sum_const, nsmul_eq_mul]
                apply le_of_eq
                congr
                exact Eq.symm (Fin.card_Iic k)
              · apply sum_le_sum
                intro i hi
                apply mem_Iic.mp at hi
                apply hmono at hi
                exact Nat.le_trans hs_le hi
        · apply prod_lt_prod
          · intro _ _ 
            apply pow_pos
            apply add_pos_of_nonneg_of_pos
            · apply Nat.cast_nonneg'
            · simp
          · intro _ h
            apply hdiv_ge
            apply Finset.mem_Iic.mp at h
            apply hmono at h
            exact Nat.le_trans hs_le h
          · obtain ⟨i, hi, hlt⟩ := h
            use i, hi
            apply hdiv_lt_of_gt_succ hlt
      -- Similarly, the right side of (1) is the product of $B=(n-k) s-$ $\left(a_{k+1}+a_{k+2}+\cdots+a_{n}\right)$ factors,
      -- all of which are at most $s$. Since $\sum_{i=1}^{n} a_{i}=n A_{n} \geq n s, A \geq B$.
      have hdiv_le {m n : ℕ} (hle : m < n) : n.factorial / (m.factorial : ℝ) < (n + 1) ^ (n - m) := by
        apply div_lt_iff₀ ?_ |>.mpr
        · norm_cast
          induction n, hle using Nat.le_induction
          · simp only [Nat.succ_eq_add_one, add_tsub_cancel_left, pow_one]
            rw [Nat.factorial_succ]
            apply Nat.mul_lt_mul_of_pos_right
            · exact lt_add_one (m + 1)
            · exact Nat.factorial_pos m
          · rename_i n hn ih
            rw [Nat.factorial_succ]
            trans (n + 1) * (n + 1) ^ (n - m) * m.factorial
            · rw [mul_assoc]
              apply Nat.mul_lt_mul_of_pos_left ih
              exact Nat.zero_lt_succ n
            · apply Nat.mul_lt_mul_of_pos_right
              · rw [←Nat.pow_add_one']
                rw [Nat.sub_add_comm]
                · apply Nat.pow_lt_pow_left
                  · exact lt_add_one (n + 1)
                  · apply ne_of_gt
                    exact Nat.zero_lt_succ (n - m)
                . exact Nat.le_of_succ_le hn
              · exact Nat.factorial_pos m
        · apply Nat.cast_pos'.mpr
          apply Nat.factorial_pos
      -- This proves the inequality. [ 5 marks to here.]
      have hRHS : ∏ i ∈ Ioi k, (s.factorial : ℝ) / (a i).factorial ≤ (s + 1) ^ ((n - 1 - k) * s - ∑ i ∈ Ioi k, a i) := by
        trans (∏ i ∈ Ioi k, (s + 1 : ℝ) ^ (s - a i))
        · apply prod_le_prod
          · intro _ _
            apply div_nonneg
            · exact Nat.cast_nonneg' s.factorial
            · apply Nat.cast_nonneg'
          · intro i h
            apply le_of_lt
            apply hdiv_le
            apply Finset.mem_Ioi.mp at h
            exact hlt_of_gt_k h
        · rw [prod_pow_eq_pow_sum]
          apply pow_le_pow_right₀
          · apply le_add_of_nonneg_left
            exact Nat.cast_nonneg' s
          · apply Nat.cast_le (α := ℝ) |>.mp
            rw [Nat.cast_sub, Nat.cast_sum, Nat.cast_sum]
            · trans ∑ x ∈ Ioi k, (s - a x : ℝ)
              · apply sum_le_sum
                intro i hi
                apply Finset.mem_Ioi.mp at hi
                rw [Nat.cast_sub]
                apply le_of_lt
                apply hlt_of_gt_k hi
              · rw [sum_sub_distrib, sum_const, Nat.cast_mul, nsmul_eq_mul]
                apply le_of_eq
                congr
                exact Fin.card_Ioi k
            · trans ∑ _ ∈ Ioi k, s
              · apply sum_le_sum
                intro i hi
                apply Finset.mem_Ioi.mp at hi
                apply le_of_lt
                apply hlt_of_gt_k hi
              · rw [sum_const, nsmul_eq_mul]
                apply le_of_eq
                congr
                exact Fin.card_Ioi k
      have hRHS_gt_of (h : ∃ i, a i < s) : ∏ i ∈ Ioi k, (s.factorial : ℝ) / (a i).factorial < (s + 1) ^ ((n - 1 - k) * s - ∑ i ∈ Ioi k, a i) := by
        apply lt_of_lt_of_le (b := (∏ i ∈ Ioi k, (s + 1 : ℝ) ^ (s - a i)))
        · apply prod_lt_prod
          · intro _ _
            apply div_pos
            · norm_cast
              apply Nat.factorial_pos s
            · apply Nat.cast_pos'.mpr
              apply Nat.factorial_pos
          · intro i h
            apply le_of_lt
            apply hdiv_le
            apply Finset.mem_Ioi.mp at h
            exact hlt_of_gt_k h
          · obtain ⟨i, hi⟩ := h
            use i
            constructor
            · apply Finset.mem_Ioi.mpr
              apply Finset.max'_lt_iff _ hne |>.mpr
              intro _ h
              apply Finset.mem_filter.mp at h
              obtain h' := h.2
              apply lt_of_lt_of_le hi at h'
              apply lt_imp_lt_of_le_imp_le ?_ h'
              intro h
              apply hmono h
            · apply hdiv_le
              apply hi
        · rw [prod_pow_eq_pow_sum]
          apply pow_le_pow_right₀
          · apply le_add_of_nonneg_left
            exact Nat.cast_nonneg' s
          · apply Nat.cast_le (α := ℝ) |>.mp
            rw [Nat.cast_sub, Nat.cast_sum, Nat.cast_sum]
            · trans ∑ x ∈ Ioi k, (s - a x : ℝ)
              · apply sum_le_sum
                intro i hi
                apply Finset.mem_Ioi.mp at hi
                rw [Nat.cast_sub]
                apply le_of_lt
                apply hlt_of_gt_k hi
              · rw [sum_sub_distrib, sum_const, Nat.cast_mul, nsmul_eq_mul]
                apply le_of_eq
                congr
                exact Fin.card_Ioi k
            · trans ∑ _ ∈ Ioi k, s
              · apply sum_le_sum
                intro i hi
                apply Finset.mem_Ioi.mp at hi
                apply le_of_lt
                apply hlt_of_gt_k hi
              · rw [sum_const, nsmul_eq_mul]
                apply le_of_eq
                congr
                exact Fin.card_Ioi k
      have hMID : (n - 1 - ↑k) * s - ∑ i ∈ Ioi k, a i ≤ ∑ i ∈ Iic k, a i - (↑k + 1) * s := by
        apply Nat.cast_le (α := ℝ) |>.mp
        rw [Nat.cast_sub, Nat.cast_sum, Nat.cast_sub, Nat.cast_sum]
        · apply sub_le_sub_iff.mpr
          rw [Nat.cast_mul, Nat.cast_mul, ←add_mul, Nat.cast_sub, Nat.cast_sub, Nat.cast_add, ←add_assoc, sub_add_cancel, sub_add_cancel]
          · rw [mul_comm]
            apply mul_le_of_le_div₀
            · apply add_nonneg
              · apply sum_nonneg
                intro _ _
                apply Nat.cast_nonneg
              · apply sum_nonneg
                intro _ _
                apply Nat.cast_nonneg
            · apply Nat.cast_nonneg
            · rw [←sum_union hdis, ←hunion, ←Nat.cast_sum, ←hA]
              unfold s
              exact Nat.floor_le hAnonneg
          · exact hn
          · apply Nat.le_sub_one_of_lt
            exact k.isLt
        · trans ∑ _ ∈ Iic k, s
          · rw [sum_const, nsmul_eq_mul]
            apply le_of_eq
            congr
            rw [Fin.card_Iic k]
            exact rfl
          · apply sum_le_sum
            intro i hi
            apply Finset.mem_Iic.mp at hi
            apply hmono at hi
            exact Nat.le_trans hs_le hi
        · trans ∑ _ ∈ Ioi k, s
          · apply sum_le_sum
            intro i hi
            apply Finset.mem_Ioi.mp at hi
            apply le_of_lt
            apply hlt_of_gt_k hi
          · rw [sum_const, nsmul_eq_mul]
            apply le_of_eq
            congr
            rw [Fin.card_Ioi k]
            exact rfl
      have hMID_gt_of (h : s < A) : (n - 1 - ↑k) * s - ∑ i ∈ Ioi k, a i < ∑ i ∈ Iic k, a i - (↑k + 1) * s := by
        apply Nat.cast_lt (α := ℝ) |>.mp
        rw [Nat.cast_sub, Nat.cast_sum, Nat.cast_sub, Nat.cast_sum]
        · apply sub_lt_sub_iff.mpr
          rw [Nat.cast_mul, Nat.cast_mul, ←add_mul, Nat.cast_sub, Nat.cast_sub, Nat.cast_add, ←add_assoc, sub_add_cancel, sub_add_cancel]
          · rw [mul_comm]
            apply lt_div_iff₀ ?_ |>.mp
            · rw [←sum_union hdis, ←hunion, ←Nat.cast_sum, ←hA]
              exact h
            · apply Nat.cast_pos'.mpr
              exact hn
          · exact hn
          · apply Nat.le_sub_one_of_lt
            exact k.isLt
        · trans ∑ _ ∈ Iic k, s
          · rw [sum_const, nsmul_eq_mul]
            apply le_of_eq
            congr
            rw [Fin.card_Iic k]
            exact rfl
          · apply sum_le_sum
            intro i hi
            apply Finset.mem_Iic.mp at hi
            apply hmono at hi
            exact Nat.le_trans hs_le hi
        · trans ∑ _ ∈ Ioi k, s
          · apply sum_le_sum
            intro i hi
            apply Finset.mem_Ioi.mp at hi
            apply le_of_lt
            apply hlt_of_gt_k hi
          · rw [sum_const, nsmul_eq_mul]
            apply le_of_eq
            congr
            rw [Fin.card_Ioi k]
            exact rfl
      have hMID_pow : (s + 1 : ℝ) ^ ((n - 1 - ↑k) * s - ∑ i ∈ Ioi k, a i) ≤ (s + 1 : ℝ) ^ (∑ i ∈ Iic k, a i - (↑k + 1) * s) := by
        apply pow_le_pow_right₀
        · apply le_add_of_nonneg_left
          exact Nat.cast_nonneg' s
        · exact hMID
      have hMID_pow_gt_of (h : s ≠ 0) (h' : s < A) : (s + 1 : ℝ) ^ ((n - 1 - ↑k) * s - ∑ i ∈ Ioi k, a i) < (s + 1 : ℝ) ^ (∑ i ∈ Iic k, a i - (↑k + 1) * s) := by
        apply pow_lt_pow_right₀
        · apply lt_add_of_pos_left
          apply Nat.cast_pos'.mpr
          exact pos_iff_ne_zero.mpr h
        · apply hMID_gt_of h'
      constructor
      · apply le_trans hRHS
        apply le_trans ?_ hLHS
        exact hMID_pow
      -- Equality in (1) holds if and only if either:
      -- (i) $A=B=0$, that is, both sides of (1) are the empty product, which occurs if and only if $a_{1}=a_{2}=\cdots=a_{n}$;
      -- or (ii) $a_{1}=1$ and $s=0$, that is, the only factors on either side of (1) are 1 's,
      -- which occurs if and only if $a_{i} \in\{0,1\}$ for all $i$. [2 marks for both (i) and (ii), no marks for (i) only.]
      constructor <;> intro heq
      · have hLHS_eq : ∏ i ∈ Iic k, (Nat.factorial (a i)) / (Nat.factorial s : ℝ) = (↑s + 1) ^ (∑ i ∈ Iic k, a i - (↑k + 1) * s) := by
          apply le_antisymm ?_ hLHS
          apply le_trans ?_ hMID_pow
          rw [heq]
          exact hRHS
        have h1 : ¬ ∃ i ∈ Iic k, a i > s + 1 := by
          intro h
          apply hLHS_gt_of at h
          rw [hLHS_eq] at h
          apply lt_self_iff_false _ |>.mp h
        push_neg at h1
        have hMID_eq : (s + 1 : ℝ) ^ ((n - 1 - ↑k) * s - ∑ i ∈ Ioi k, a i) = (s + 1 : ℝ) ^ (∑ i ∈ Iic k, a i - (↑k + 1) * s) := by
          apply le_antisymm hMID_pow
          rw [←hLHS_eq, heq]
          exact hRHS
        have h2 : s = 0 ∨ s ≥ A := by
          by_contra h
          push_neg at h
          obtain ⟨h₁, h₂⟩ := h
          apply hMID_pow_gt_of h₁ at h₂
          rw [hMID_eq] at h₂
          apply lt_self_iff_false _ |>.mp h₂
        have hRHS_eq : ∏ i ∈ Ioi k, (s.factorial : ℝ) / (a i).factorial = (s + 1 : ℝ) ^ ((n - 1 - ↑k) * s - ∑ i ∈ Ioi k, a i) := by
          apply le_antisymm hRHS
          rw [hMID_eq, ←heq, hLHS_eq]
        have h3 : ¬ ∃ i, a i < s := by
          intro h
          apply hRHS_gt_of at h
          rw [hRHS_eq] at h
          apply lt_self_iff_false _ |>.mp h
        push_neg at h3
        rcases h2 with h2 | h2
        · left
          intro i
          have : i ∈ Iic k := by
            apply mem_Iic.mpr
            apply Finset.le_max'
            apply mem_filter.mpr
            constructor
            · apply mem_univ
            · apply h3
          rw [h2] at h1
          apply h1 at this
          norm_num at this
          exact this
        · right
          use s
          intro i
          apply le_antisymm ?_ (h3 i)
          by_contra h
          push_neg at h
          have : ((∑ i, a i : ℕ) : ℝ) > ∑ _ : Fin n, s := by
            apply Nat.cast_lt.mpr
            apply sum_lt_sum
            · intro i _
              apply h3
            · use i
              constructor
              · apply mem_univ
              · apply h
          apply eq_div_iff (by norm_cast; exact Nat.not_eq_zero_of_lt hn) |>.mp at hA
          rw [←hA, sum_const, nsmul_eq_mul, Nat.cast_mul, card_univ, Fintype.card_fin, mul_comm] at this
          have : n * A > n * A := by
            apply lt_of_le_of_lt ?_ this
            trans (n : ℝ) * s
            · apply mul_le_mul_of_nonneg_left
              · exact h2
              · apply Nat.cast_nonneg
            · rfl
          apply mul_lt_mul_left (by norm_cast) |>.mp at this
          apply lt_self_iff_false _ |>.mp this
      · rcases heq with h | h
        · -- or (ii) $a_{1}=1$ and $s=0$, that is, the only factors on either side of (1) are 1 's,
          have ha {i : Fin n} : (a i).factorial = 1 := by
            obtain h := h i
            exact Nat.factorial_eq_one.mpr h
          have hs : s.factorial = 1 := by
            have hA : A ≤ 1 := by
              rw [hA]
              apply div_le_iff₀ ?_ |>.mpr
              · rw [one_mul]
                apply Nat.cast_le.mpr
                trans ∑ _ : Fin n, 1
                · apply sum_le_sum
                  intro i _
                  apply h
                · rw [sum_const, Finset.card_univ, Fintype.card_fin]
                  simp only [smul_eq_mul, mul_one, le_refl]
              · apply Nat.cast_pos'.mpr hn
            have hs : s ≤ 1 := by
              exact Nat.floor_le_one_of_le_one hA
            exact Nat.factorial_eq_one.mpr hs
          have h₁ : ∀ i ∈ Iic k, ((a i).factorial : ℝ) / (s.factorial) = 1 := by
            intro _ _
            rw [ha, hs]
            simp only [Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]
          rw [prod_congr rfl h₁]
          have h₂ : ∀ i ∈ Ioi k, (s.factorial) / ((a i).factorial : ℝ) = 1 := by
            intro _ _
            rw [ha, hs]
            simp only [Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]
          rw [prod_congr rfl h₂]
          rw [prod_const, prod_const, one_pow, one_pow]
        · -- (i) $A=B=0$, that is, both sides of (1) are the empty product, which occurs if and only if $a_{1}=a_{2}=\cdots=a_{n}$;
          obtain ⟨b, hb⟩ := h
          have hs : s = b := by
            have hA : A = b := by
              rw [hA]
              simp [hb]
              rw [mul_div_cancel_left₀]
              apply ne_of_gt
              apply Nat.cast_pos'.mpr
              exact hn
            unfold s
            rw [hA]
            exact Nat.floor_natCast b
          simp [hb, hs]
          rw [div_self, one_pow, one_pow]
          apply ne_of_gt
          apply Nat.cast_pos'.mpr
          exact Nat.factorial_pos b
