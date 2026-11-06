import Mathlib

theorem inequalities_221083 (x : Fin 9 → ℝ)
    (h₀ : ∀ i, 0 ≤ x i)
    (h₁ : ∑ i, x i ^ 2 ≥ 25) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ 5 ≤ x i + x j + x k := by
  -- Решение. Без ограничување на општоста можеме да претпоставиме дека
  -- $$ x_{1} \geq x_{2} \geq x_{3} \geq x_{4} \geq x_{5} \geq x_{6} \geq x_{7} \geq x_{8} \geq x_{9} \geq 0 $$
  wlog hanti : Antitone x with H
  · let x' (i : Fin 9) := ((List.ofFn x).insertionSort (fun r₁ r₂ => r₁ ≥ r₂)).get ⟨i.1, by rw [List.length_insertionSort]; simp⟩
    have hsorted : ((List.ofFn x).insertionSort (fun r₁ r₂ => r₁ ≥ r₂)).Sorted (fun r₁ r₂ => r₁ ≥ r₂) := by
      exact List.sorted_insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) (List.ofFn x)
    have hmono : Antitone x' := by
      intro i j hij
      unfold x'
      exact List.Sorted.rel_get_of_le hsorted hij
    have hx' : ∀ i, 0 ≤ x' i := by
      intro i
      apply le_trans (b := x' 8)
      · have : x' 8 ∈ List.ofFn x := by
          unfold x'
          apply List.mem_insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) |>.mp
          apply List.get_mem
        obtain ⟨j, hj⟩ := List.get_of_mem this
        rw [List.get_ofFn] at hj
        rw [←hj]
        apply h₀
      · apply hmono
        obtain ⟨i, hi⟩ := i
        exact Fin.succ_le_succ_iff.mp hi
    -- prove there exists a bijection between the two lists
    obtain hperm := List.perm_insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) (List.ofFn x)
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
    -- We can now use the bijection to show that the sequence of coefficients $a_{k}$ is a solution.
    obtain ⟨f, hb, hf⟩ := bijection_of_perm (List.Perm.symm hperm)
    let g (i : Fin 9) : Fin 9 := ⟨f i, by apply lt_of_lt_of_eq (f i).2; rw [List.length_insertionSort]; simp⟩
    have hb : Function.Bijective g := by
      constructor
      · intro x y h
        simp [g] at h
        apply hb.1
        exact Fin.eq_of_val_eq h
      · intro y
        obtain ⟨x, hx⟩ := hb.2 ⟨y.1, by apply lt_of_lt_of_eq y.2; rw [List.length_insertionSort]; simp⟩
        use x
        simp [g, hx]
    have hg : ∀ i, x i = x' (g i) := by
      intro i
      trans List.get (List.ofFn x) i
      · rw [List.get_ofFn]
        congr
      · rw [hf]
    have h₁' : ∑ i, x' i ^ 2 ≥ 25 := by
      apply le_of_le_of_eq h₁
      trans ∑ i, x' (g i) ^ 2
      · apply Finset.sum_congr
        · simp
        · intro i _
          rw [←hg]
      · have : Finset.univ.image g = Finset.univ := Finset.image_univ_of_surjective hb.2
        nth_rw 2 [←this]
        rw [Finset.sum_image]
        intro _ _ _ _ h
        exact hb.1 h
    let ⟨r, hr₁, hr₂⟩ := Function.bijective_iff_has_inverse.mp hb
    obtain ⟨i, j, k, hne₁, hne₂, hne₃, hge⟩ := H x' hx' h₁' hmono
    use r i, r j, r k
    split_ands
    on_goal -1 =>
      apply le_of_le_of_eq hge
      rw [hg, hg, hg, hr₂, hr₂, hr₂]
    all_goals
      intro h
      apply congrArg g at h
      rw [hr₂, hr₂] at h
      contradiction
  · use 0, 1, 2
    simp
    apply pow_le_pow_iff_left₀ ?_ ?_ (show 2 ≠ 0 by simp) |>.mp
    · norm_num
      apply le_trans h₁
      rw [Fin.sum_univ_succ, Fin.sum_univ_eight]
      rw [add_sq, add_sq, mul_add, add_mul]
      simp [Fin.succ]
      -- Тогаш имаме: $x_{1} x_{2} \geq x_{4}^{2} \geq x_{5}^{2}, x_{1} x_{3} \geq x_{6}^{2} \geq x_{7}^{2}$ и $x_{2} x_{3} \geq x_{8}^{2} \geq x_{9}^{2}$, па затоа
      -- $$ \begin{aligned} \left(x_{1}+x_{2}+x_{3}\right)^{2} & =x_{1}^{2}+x_{2}^{2}+x_{3}^{2}+2 x_{1} x_{2}+2 x_{1} x_{3}+2 x_{2} x_{3} \ & \geq x_{1}^{2}+x_{2}^{2}+x_{3}^{2}+x_{4}^{2}+x_{5}^{2}+x_{6}^{2}+x_{7}^{2}+x_{8}^{2}+x_{9}^{2} \geq 25 \end{aligned} $$
      have hge₁ : x 0 * x 1 ≥ x 3 ^ 2 := by
        rw [sq]
        gcongr
        any_goals apply h₀
        all_goals apply hanti; simp
      have hge₂ : x 0 * x 1 ≥ x 4 ^ 2 := by
        apply le_trans ?_ hge₁
        apply sq_le_sq.mpr
        rw [abs_of_nonneg (h₀ _), abs_of_nonneg (h₀ _)]
        apply hanti
        simp
      have hge₃ : x 0 * x 2 ≥ x 5 ^ 2 := by
        rw [sq]
        gcongr
        any_goals apply h₀
        all_goals apply hanti; simp
      have hge₄ : x 0 * x 2 ≥ x 6 ^ 2 := by
        apply le_trans ?_ hge₃
        apply sq_le_sq.mpr
        rw [abs_of_nonneg (h₀ _), abs_of_nonneg (h₀ _)]
        apply hanti
        simp
      have hge₅ : x 1 * x 2 ≥ x 7 ^ 2 := by
        rw [sq]
        gcongr
        any_goals apply h₀
        all_goals apply hanti; simp
      have hge₆ : x 1 * x 2 ≥ x 8 ^ 2 := by
        apply le_trans ?_ hge₅
        apply sq_le_sq.mpr
        rw [abs_of_nonneg (h₀ _), abs_of_nonneg (h₀ _)]
        apply hanti
        simp
      -- т.е. $x_{1}+x_{2}+x_{3} \geq 5$.
      linarith only [hge₁, hge₂, hge₃, hge₄, hge₅, hge₆]
    · simp
    · linarith only [h₀ 0, h₀ 1, h₀ 2]
