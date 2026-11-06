import Mathlib

open Finset Real

/- Soit $n$ un entier strictement positif et $x_{1}, \ldots, x_{n}$ des réels strictement positifs. Montrer qu'il existe des nombres $a_{1}, \ldots, a_{n} \in\{-1,1\}$ tels que :

$$
a_{1} x_{1}^{2}+a_{2} x_{2}^{2}+\cdots+a_{n} x_{n}^{2} \geqslant\left(a_{1} x_{1}+a_{2} x_{2}+\cdots+a_{n} x_{n}\right)^{2} .
$$ -/
theorem inequalities_604798 (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    ∃ a : Fin n → ℤ, (∀ i, a i ∈ ({-1, 1} : Finset ℤ)) ∧ (∑ i, a i * x i ^ 2) ≥ (∑ i, a i * x i) ^ 2 := by
  -- Let's order the reals $x_{k}$ so that $x_{1} \geq x_{2} \geq \ldots \geq x_{n}&gt;0$.
  wlog h : Antitone x with H
  · -- if not, we can sort the sequence
    let x' := ((List.ofFn x).insertionSort (fun r₁ r₂ => r₁ ≥ r₂)).get
    have hsorted : ((List.ofFn x).insertionSort (fun r₁ r₂ => r₁ ≥ r₂)).Sorted (fun r₁ r₂ => r₁ ≥ r₂) := by
      exact List.sorted_insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) (List.ofFn x)
    have hmono : Antitone x' := by
      intro i j hij
      simp [x']
      exact List.Sorted.rel_get_of_le hsorted hij
    have hx' : ∀ i, 0 < x' i := by
      intro i
      apply lt_of_lt_of_le (b := x' ⟨(List.insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) (List.ofFn x)).length - 1, by simp [hn]⟩)
      · simp[x']
        have : (List.insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) (List.ofFn x))[(List.insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) (List.ofFn x)).length - 1]'(by simp [hn]) ∈ (List.ofFn x) := by
          apply List.mem_insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) |>.mp
          simp
        apply List.mem_ofFn _ _ |>.mp at this
        obtain ⟨j, hj⟩ := this
        simp at hj
        rw [←hj]
        exact hx j
      · apply hmono
        obtain ⟨i, hi⟩ := i
        simp
        refine (Nat.le_sub_one_iff_lt hn).mpr ?hbc.a.mk.a
        simp at hi
        exact hi
    obtain ⟨a, ha, hge⟩ := H (List.insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) (List.ofFn x)).length (by simp [hn]) x' hx' hmono
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
    let a' (i : Fin n) : ℤ := a (f ⟨i.val, by simp⟩)
    use a'
    constructor
    · intro i
      apply ha
    · have h1 :  ∑ i : Fin n, ↑(a' i) * x i ^ 2 =  ∑ i : Fin (List.insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) (List.ofFn x)).length, ↑(a i) * x' i ^ 2 := by
        trans ∑ i : Fin n, ↑(a' i) * (x' (f ⟨i, by simp⟩)) ^ 2
        · apply Finset.sum_congr rfl
          intro i _
          congr
          simp only [x']
          rw [←hf]
          simp
        · unfold a'
          have : Finset.univ = Finset.univ.image (fun i : Fin n => f ⟨i, by simp⟩) := by
            symm
            refine image_univ_of_surjective ?_
            intro y
            obtain ⟨a, ha⟩ := hb.2 y
            use ⟨a.1, by apply lt_of_lt_of_eq a.2; simp⟩
          rw [this, Finset.sum_image]
          intro x _ y _ h
          apply hb.1 at h
          simp at h
          exact Fin.eq_of_val_eq h
      have h2 : ∑ i : Fin n, ↑(a' i) * x i =  ∑ i : Fin (List.insertionSort (fun r₁ r₂ ↦ r₁ ≥ r₂) (List.ofFn x)).length, ↑(a i) * x' i := by
        trans ∑ i : Fin n, ↑(a' i) * (x' (f ⟨i, by simp⟩))
        · apply Finset.sum_congr rfl
          intro i _
          congr
          simp only [x']
          rw [←hf]
          simp
        · unfold a'
          have : Finset.univ = Finset.univ.image (fun i : Fin n => f ⟨i, by simp⟩) := by
            symm
            refine image_univ_of_surjective ?_
            intro y
            obtain ⟨a, ha⟩ := hb.2 y
            use ⟨a.1, by apply lt_of_lt_of_eq a.2; simp⟩
          rw [this, Finset.sum_image]
          intro x _ y _ h
          apply hb.1 at h
          simp at h
          exact Fin.eq_of_val_eq h
      rw [h1, h2]
      exact hge
  · -- We will show by strong induction that a solution is provided by the sequence of coefficients defined by $a_{k}=1$ if $k$ is odd
    -- and $a_{k}=-1$ if $k$ is even.
    let a (i : Fin n) := if i.val % 2 = 0 then 1 else -1
    use a
    constructor
    · simp [a]
      exact fun i ↦ Or.symm (Nat.mod_two_eq_zero_or_one ↑i)
    · -- prove that the prefix sum of the sequence is nonnegative
      have haddnonneg {m : ℕ} (hm : m < n) : ∑ i ∈ filter (fun i : Fin n ↦ i.1 ≤ m) univ, (a i) * x i ≥ 0 := by
        induction m using Nat.strongRecOn
        rename_i m ih
        by_cases hm' : m ≤ 1
        · interval_cases m
          · have : filter (fun i : Fin n ↦ i.1 = 0) Finset.univ = {⟨0, by assumption⟩} := by
              ext ⟨i, hi⟩
              simp
            simp [this, a]
            apply le_of_lt
            apply hx
          · have : filter (fun i : Fin n ↦ i.1 ≤ 1) Finset.univ = {⟨0, by assumption⟩, ⟨1, by assumption⟩} := by
              ext ⟨i, hi⟩
              simp
              exact Nat.le_one_iff_eq_zero_or_eq_one
            simp [this, a]
            apply h
            simp
        · have hm' : m ≥ 2 := by simp at hm'; exact hm'
          have : filter (fun i : Fin n ↦ i.1 ≤ m) Finset.univ = filter (fun i : Fin n ↦ i.1 ≤ m - 1) Finset.univ ∪ {⟨m, hm⟩} := by
            ext ⟨i, hi⟩
            simp
            constructor <;> intro h
            · rcases lt_or_eq_of_le h with (h | h)
              · left; exact Nat.le_sub_one_of_lt h
              · simp [h]
            · rcases h with h | h
              · apply le_trans h
                simp
              · simp [h]
          have hdis : Disjoint (filter (fun i : Fin n ↦ i.1 ≤ m - 1) Finset.univ) {⟨m, hm⟩} := by simp; exact Nat.zero_lt_of_lt hm'
          rw [this, Finset.sum_union hdis]
          by_cases h1 : m % 2 = 0
          · simp [a, h1]
            apply add_nonneg
            · simp [a] at ih
              apply ih
              exact Nat.sub_one_lt_of_lt hm'
              exact tsub_lt_of_lt hm
            · apply le_of_lt
              apply hx
          · have : filter (fun i : Fin n ↦ i.1 ≤ m - 1) Finset.univ = filter (fun i : Fin n ↦ i.1 ≤ m - 2) Finset.univ ∪ {⟨m - 1, by exact tsub_lt_of_lt hm⟩} := by
              ext ⟨i, hi⟩
              simp
              constructor <;> intro h
              · rcases lt_or_eq_of_le h with (h | h)
                · left; exact Nat.le_sub_one_of_lt h
                · simp [h]
              · rcases h with h | h
                · apply le_trans h
                  simp
                  rw [show 2 = 1 + 1 by rfl, ←Nat.add_assoc, Nat.sub_add_cancel]
                  · simp
                  · exact Nat.one_le_of_lt hm'
                · simp [h]
            have hdis : Disjoint (filter (fun i : Fin n ↦ i.1 ≤ m - 2) Finset.univ) {⟨m - 1, by exact tsub_lt_of_lt hm⟩} := by
              simp
              rw [show 2 = 1 + 1 by rfl, Nat.sub_add_eq, Nat.sub_add_cancel]
              · simp
                exact Nat.zero_lt_of_lt hm'
              · exact Nat.le_sub_one_of_lt hm'
            rw [this, Finset.sum_union hdis]
            simp [a]
            rw [add_assoc]
            apply add_nonneg
            · simp [a] at ih
              apply ih
              refine Nat.sub_lt_self ?_ hm'
              simp
              exact tsub_lt_of_lt hm
            · simp [h1]
              have h2 : (m - 1) % 2 = 0 := by
                refine Nat.even_iff.mp ?_
                refine Nat.Odd.sub_odd ?hm ?hn
                · refine Nat.odd_iff.mpr ?hm.a
                  simp at h1
                  exact h1
                · simp
              simp [h2]
              apply h
              simp
      have {m : ℕ} (hm : m < n) : ∑ i ∈ Finset.univ.filter (fun i => i.1 ≤ m), ↑(a i) * x i ^ 2 ≥ (∑ i ∈ Finset.univ.filter (fun i => i.1 ≤ m), ↑(a i) * x i) ^ 2 := by
        induction m using Nat.strongRecOn
        rename_i m ih
        by_cases hm : m ≤ 1
        · interval_cases m
          · -- If $n=1, a_{1} x_{1}^{2}=\left(a_{1} x_{1}\right)^{2}$, so the inequality is satisfied.
            simp [a]
            have : filter (fun i : Fin n ↦ i.1 = 0) Finset.univ = {⟨0, by assumption⟩} := by
              ext ⟨i, hi⟩
              simp
            simp [this]
          · -- If $n=2, a_{1} x_{1}^{2}+a_{2} x_{2}^{2}=x_{1}^{2}-x_{2}^{2} \geq x_{1}^{2}-2 x_{1} x_{2}+x_{2}^{2}=\left(x_{1}-x_{2}\right)^{2}$
            -- since $x_{1} \geq x_{2}$; the inequality is still satisfied.
            simp [a]
            have : filter (fun i : Fin n ↦ i.1 ≤ 1) Finset.univ = {⟨0, by assumption⟩, ⟨1, by assumption⟩} := by
              ext ⟨i, hi⟩
              simp
              exact Nat.le_one_iff_eq_zero_or_eq_one
            simp [this]
            apply sub_nonneg.mp
            ring_nf
            simp
            rw [sq]
            apply mul_le_mul_of_nonneg_right
            · apply h
              simp
            · apply le_of_lt
              apply hx
        · simp at hm
          -- Let $n \geq 3$.
          -- Suppose the result is established up to rank $n-1$ and show the inequality at rank $n$.
          -- The difference between the two members is then
          -- $$ a_{1} x_{1}^{2}+\ldots+a_{n} x_{n}^{2}-\left(a_{1} x_{1}+\ldots+a_{n} x_{n}\right)^{2}=\alpha x_{1}+\beta $$
          have : filter (fun i : Fin n ↦ i.1 ≤ m) Finset.univ = filter (fun i : Fin n ↦ i.1 ≤ m - 1) Finset.univ ∪ {⟨m, by assumption⟩} := by
            ext ⟨i, hi⟩
            simp
            constructor <;> intro h
            · rcases lt_or_eq_of_le h with (h | h)
              · left; exact Nat.le_sub_one_of_lt h
              · simp [h]
            · rcases h with h | h
              · trans m - 1
                · exact h
                · simp
              · simp [h]
          have hdis : Disjoint (filter (fun i : Fin n ↦ i.1 ≤ m - 1) Finset.univ) {⟨m, by assumption⟩} := by simp; exact Nat.zero_lt_of_lt hm
          rw [this, Finset.sum_union hdis, Finset.sum_union hdis]
          simp
          · -- with $$ \alpha=-2\left(a_{2} x_{2}+\ldots+a_{n} x_{n}\right)=2\left(\left(x_{2}-x_{3}\right)+\left(x_{4}-x_{5}\right)+\ldots\right) \leq 0 $$
            -- since $x_{2} \geq x_{3}, x_{4} \geq x_{5}, \ldots$ Therefore, using the increasing function $x \mapsto \alpha x+\beta$ and $x_{1} \geq x_{2}$,
            -- $$ \begin{aligned} a_{1} x_{1}^{2}+\ldots+a_{n} x_{n}^{2}-\left(a_{1} x_{1}+\ldots+a_{n} x_{n}\right)^{2} & \geq \alpha x_{2}+\beta \ & \geq a_{1} x_{2}^{2}+a_{2} x_{2}^{2} \ldots+a_{n} x_{n}^{2}-\left(a_{1} x_{2}+a_{2} x_{2}+\ldots+a_{n} x_{n}\right)^{2} \ & \geq a_{3} x_{1}^{3}+\ldots+a_{n} x_{n}^{2}-\left(a_{3} x_{3}+\ldots+a_{n} x_{n}\right)^{2} \end{aligned} $$
            -- since $a_{1}=-a_{2}$ and thus $a_{1} x_{1}^{2}+a_{2} x_{2}^{2}=a_{1} x_{1}+a_{2} x_{2}=0$. The last term is positive according to the induction hypothesis with the reals $x_{3}, \ldots, x_{n}$, which completes the proof of the inequality at rank $n$.
            by_cases h1 : m % 2 = 0
            · have heq' : filter (fun i : Fin n ↦ i.1 ≤ m - 1) Finset.univ = filter (fun i : Fin n ↦ i.1 ≤ m - 2) univ ∪ {⟨m - 1, by apply tsub_lt_of_lt; assumption⟩} := by
                ext ⟨i, hi⟩
                simp
                constructor <;> intro h
                · rcases lt_or_eq_of_le h with (h | h)
                  · left; exact Nat.le_sub_one_of_lt h
                  · simp [h]
                · rcases h with h | h
                  · apply le_trans h
                    simp
                    rw [show 2 = 1 + 1 by rfl, ←Nat.add_assoc, Nat.sub_add_cancel]
                    · simp
                    · apply le_of_lt hm
                  · simp [h]
              have hdis' : Disjoint (filter (fun i : Fin n ↦ i.1 ≤ m - 2) univ) {⟨m - 1, by apply tsub_lt_of_lt; assumption⟩} := by
                simp
                rw [show 2 = 1 + 1 by rfl, ←Nat.sub_sub, Nat.sub_add_cancel]
                · exact Nat.sub_one_lt_of_lt hm
                · exact Nat.le_sub_one_of_lt hm
              rw [heq', Finset.sum_union hdis', Finset.sum_union hdis']
              simp
              trans (∑ i ∈ filter (fun i : Fin n ↦ ↑i ≤ m - 2) univ, ↑(a i) * x i) ^ 2 + (↑(a ⟨m - 1, by apply tsub_lt_of_lt; assumption⟩) * x ⟨m - 1, by apply tsub_lt_of_lt; assumption⟩ ^ 2)
                  + ↑(a ⟨m, by assumption⟩) * x ⟨m, by assumption⟩ ^ 2
              · simp [a, h1]
                have h2 : (m - 1) % 2 = 1 := by
                  refine Nat.odd_iff.mp ?_
                  refine Nat.Even.sub_odd ?_ ?_ ?_
                  · apply le_of_lt hm
                  · exact Nat.even_iff.mpr h1
                  · exact Nat.odd_iff.mpr rfl
                simp [h2]
                trans ((∑ i ∈ filter (fun i : Fin n ↦ ↑i ≤ m - 2) univ, if i.1 % 2 = 0 then x i else -x i) + (-x ⟨m - 1, by apply tsub_lt_of_lt; assumption⟩ + x ⟨m, by assumption⟩)) ^ 2
                · apply le_of_eq
                  ring
                · rw [add_sq, add_assoc, add_assoc]
                  apply add_le_add_left
                  rw [add_sq, ←add_assoc]
                  apply add_le_add_right
                  rw [neg_sq]
                  apply sub_nonneg.mp
                  rw [sub_add_eq_sub_sub, sub_add_eq_sub_sub]
                  trans 2 * ((∑ i ∈ filter (fun i : Fin n ↦ ↑i ≤ m - 2) univ, if i.1 % 2 = 0 then x i else -x i) - x ⟨m - 1, by apply tsub_lt_of_lt; assumption⟩) * (x ⟨m - 1, by apply tsub_lt_of_lt; assumption⟩ - x ⟨m, by assumption⟩)
                  · apply mul_nonneg
                    · apply mul_nonneg
                      · simp
                      · obtain h := haddnonneg (show m - 1 < n by apply tsub_lt_of_lt; assumption)
                        rw [heq', Finset.sum_union hdis'] at h
                        simp [a, h1, h2] at h
                        simp
                        exact h
                    · simp
                      apply h
                      simp
                  · apply le_of_eq
                    ring
              · obtain ih := ih (m - 2) (by refine Nat.sub_lt_self ?h₀ hm; simp) (by apply tsub_lt_of_lt; assumption)
                rel [ih]
            · obtain ih := ih (m - 1) (by exact Nat.sub_one_lt_of_lt hm) (by apply tsub_lt_of_lt; assumption)
              trans (∑ i ∈ filter (fun i : Fin n ↦ ↑i ≤ m - 1) univ, ↑(a i) * x i) ^ 2 + ↑(a ⟨m, by assumption⟩) * x ⟨m, by assumption⟩ ^ 2
              · simp [a]
                simp [h1]
                apply sub_nonneg.mp
                rw [add_sq, sub_add_eq_sub_sub, sub_add_eq_sub_sub, sub_add_eq_sub_sub]
                ring_nf
                simp
                apply le_sub_left_of_add_le
                rw [sq, ←add_mul]
                apply mul_le_mul_of_nonneg_right
                · ring_nf
                  apply mul_le_mul_of_nonneg_right
                  · obtain hn := haddnonneg (show m < n by assumption)
                    rw [this, Finset.sum_union hdis] at hn
                    simp [a, h1] at hn
                    exact hn
                  · simp
                · apply le_of_lt
                  apply hx
              · rel [ih]
      -- We can now conclude the proof by let m = n - 1.
      obtain h := this (show n - 1 < n by simp; assumption)
      have h₁ : ∑ i ∈ filter (fun i ↦ i.1 ≤ n - 1) Finset.univ, ↑(a i) * x i ^ 2 = ∑ i : Fin n, ↑(a i) * x i ^ 2 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        have : i.1 ≤ n - 1 := by apply Nat.le_sub_one_iff_lt ?_ |>.mpr; exact i.2; assumption
        simp [this]
      have h₂ : ∑ i ∈ filter (fun i ↦ i.1 ≤ n - 1) Finset.univ, ↑(a i) * x i = ∑ i : Fin n, ↑(a i) * x i := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        have : i.1 ≤ n - 1 := by apply Nat.le_sub_one_iff_lt ?_ |>.mpr; exact i.2; assumption
        simp [this]
      rw [h₁, h₂] at h
      exact h
