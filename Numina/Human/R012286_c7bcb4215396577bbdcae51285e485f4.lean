import Mathlib
set_option maxHeartbeats 0

open Finset Real

/--
  Given $0 < a_{i} \leqslant \frac{1}{2}(i=1,2, \cdots, n)$.
  Prove:
  $$
  \begin{array}{l}
  \frac{\sum_{i=1}^{n} a_{i}^{2}}{\sum_{i=1}^{n} a_{i}}-\sqrt[n]{\prod_{i=1}^{n} a_{i}} \\
  \geqslant \frac{\sum_{i=1}^{n}\left(1-a_{i}\right)^{2}}{\sum_{i=1}^{n}\left(1-a_{i}\right)}-\sqrt[n]{\prod_{i=1}^{n}\left(1-a_{i}\right)} .
  \end{array}$$
-/
theorem inequalities_223230 {n : ℕ} (hn : n ≥ 1) {a : Fin n → ℝ} (ha : ∀ i, a i ∈ Set.Ioc 0 (1 / 2)) :
    (∑ i, a i ^ 2) / (∑ i, a i) - (∏ i, a i) ^ (1 / n : ℝ) ≥
    (∑ i, (1 - a i) ^ 2) / (∑ i, (1 - a i)) - (∏ i, (1 - a i)) ^ (1 / n : ℝ) := by
  simp only [Set.mem_Ioc] at ha
  obtain ha₁ := fun {i} => (ha i).1
  obtain ha₂ := fun {i} => (ha i).2
  -- Prove that the original inequality is equivalent to:
  -- $$ \begin{array}{c} \frac{n \sum_{i=1}^{n} a_{i}^{2}}{\sum_{i=1}^{n} a_{i}}-\sum_{i=1}^{n} a_{i}+\sum_{i=1}^{n} a_{i}-n \sqrt[n]{\prod_{i=1}^{n} a_{i}} \ \geqslant \frac{n \sum_{i=1}^{n}\left(1-a_{i}\right)^{2}}{\sum_{i=1}^{n}\left(1-a_{i}\right)}-\sum_{i=1}^{n}\left(1-a_{i}\right)+ \ \sum_{i=1}^{n}\left(1-a_{i}\right)-n \sqrt[n]{\prod_{i=1}^{n}\left(1-a_{i}\right)} . \end{array} $$
  suffices h : n * (∑ i, a i ^ 2) / (∑ i, a i) - ∑ i, a i + (∑ i, a i - n * (∏ i, a i) ^ (1 / n : ℝ)) ≥
    n * (∑ i, (1 - a i) ^ 2) / (∑ i, (1 - a i)) - ∑ i, (1 - a i) + (∑ i, (1 - a i) - n * (∏ i, (1 - a i)) ^ (1 / n : ℝ))
  · rw [←add_sub_assoc, ←add_sub_assoc] at h
    rw [sub_add_cancel, sub_add_cancel] at h
    apply le_of_mul_le_mul_of_pos_left (a := (n : ℝ))
    · apply le_of_eq_of_le ?_ (le_of_le_of_eq h ?_)
      all_goals ring
    · apply Nat.cast_pos.mpr
      exact hn
  · have : ∑ i, a i > 0 := by
      -- Prove that the sum of $a_i$ is positive.
      apply Finset.sum_pos
      · intro i _
        apply ha₁
      · refine univ_nonempty_iff.mpr ?_
        exact Fin.pos_iff_nonempty.mp hn
    have : ∑ i, (1 - a i) > 0 := by
      -- Prove that the sum of $1 - a_i$ is positive.
      apply Finset.sum_pos
      · intro i _
        simp
        apply lt_of_le_of_lt ha₂
        norm_num
      · refine univ_nonempty_iff.mpr ?_
        exact Fin.pos_iff_nonempty.mp hn
    have h₁ : n * (∑ i, a i ^ 2) / (∑ i, a i) - ∑ i, a i ≥ n * (∑ i, (1 - a i) ^ 2) / (∑ i, (1 - a i)) - ∑ i, (1 - a i) := by
      -- Note that:
      -- $$ \begin{array}{l} \frac{n \sum_{i=1}^{n} a_{i}^{2}}{\sum_{i=1}^{n} a_{i}}-\sum_{i=1}^{n} a_{i}=\frac{\sum_{1 \leq i < j \leq n}\left(a_{i}-a_{j}\right)^{2}}{\sum_{i=1}^{n} a_{i}}, \ \frac{n \sum_{i=1}^{n}\left(1-a_{i}\right)^{2}}{\sum_{i=1}^{n}\left(1-a_{i}\right)}-\sum_{i=1}^{n}\left(1-a_{i}\right) \ =\frac{\sum_{1 \leq i< j \leq n}\left(\left(1-a_{i}\right)-\left(1-a_{j}\right)\right)^{2}}{\sum_{i=1}^{n}\left(1-a_{i}\right)} \ =\frac{\sum_{1 \leq i< j \in n}\left(a_{i}-a_{j}\right)^{2}}{\sum_{i=1}^{n}\left(1-a_{i}\right)} . \end{array} $$
      have hlem {a : Fin n → ℝ} :  ∑ i : Fin n, ∑ j ∈ Iio i, (a i - a j) ^ 2 = ↑n * ∑ i : Fin n, a i ^ 2 - (∑ i : Fin n, a i) * ∑ i : Fin n, a i := by
        -- Prove the equivalence of the above summation formula.
        trans  ∑ i : Fin n, ∑ j ∈ Iio i, a i ^ 2 + ∑ i, ∑ j ∈ Iio i, a j ^ 2 - ∑ i, ∑ j ∈ Iio i, 2 * a i * a j
        · rw [←sum_add_distrib, ←sum_sub_distrib]
          congr; ext i
          rw [←sum_add_distrib, ←sum_sub_distrib]
          congr; ext j
          ring
        trans  ∑ i : Fin n, i * a i ^ 2 + ∑ j, ∑ i ∈ Ioi j, a j ^ 2 - ∑ i, ∑ j ∈ Iio i, 2 * a i * a j
        · congr 1
          congr 1
          · congr; ext i; simp
          · rw [Finset.sum_comm']
            intro i j
            simp
        trans ∑ i : Fin n, i * a i ^ 2 + ∑ j, (n - 1 - j) * a j ^ 2 - ∑ i, ∑ j ∈ Iio i, 2 * a i * a j
        · congr; ext j; simp
          left
          rw [Nat.cast_sub, Nat.cast_sub hn]
          · simp
          · apply Nat.le_sub_one_of_lt j.2
        trans (n - 1) * ∑ i : Fin n, a i ^ 2 - ∑ i, ∑ j ∈ Iio i, 2 * a i * a j
        · rw [←sum_add_distrib, mul_sum]
          congr; ext i
          ring
        · have : ∑ i : Fin n, ∑ j : Fin n, a i * a j = ∑ i, a i ^ 2 + ∑ i, ∑ j ∈ Iio i, 2 * a i * a j := by
            trans ∑ i : Fin n, ∑ j ∈ Iio i ∪ {i} ∪ Ioi i, a i * a j
            · congr; ext i
              congr; ext j
              simp
              exact lt_trichotomy j i
            trans ∑ i : Fin n, (∑ j ∈ Iio i, a i * a j + a i ^ 2 + ∑ j ∈ Ioi i, a i * a j)
            · congr; ext i
              rw [sum_union, sum_union]
              · simp; ring
              · simp
              · simp
                exact Disjoint.symm (disjoint_Ioi_Iio i)
            · rw [sum_add_distrib, sum_add_distrib]
              rw [sum_comm' (t := fun i => Ioi i) (t' := univ) (s' := fun i => Iio i)]
              · trans ∑ x : Fin n, ∑ j ∈ Iio x, a x * a j + ∑ x : Fin n, a x ^ 2 + ∑ y : Fin n, ∑ x ∈ Iio y, a y * a x
                · congr; ext i
                  congr; ext j
                  ring
                · apply sub_eq_zero.mp
                  ring_nf
                  rw [sum_mul, ←sum_sub_distrib]
                  apply sum_eq_zero
                  intro _ _
                  rw [sum_mul, ←sum_sub_distrib]
                  apply sum_eq_zero
                  intro _ _
                  ring
              · intro i j
                simp
          rw [sum_mul_sum, this]
          apply sub_eq_zero.mp
          ring_nf
       -- Therefore, since $0 < a_i \leqslant \frac{1}{2}$, we have:
       -- $$ \begin{array}{l} \frac{n \sum_{i=1}^{n} a_{i}^{2}}{\sum_{i=1}^{n} a_{i}}-\sum_{i=1}^{n} a_{i} \ \geqslant \frac{n \sum_{i=1}^{n}\left(1-a_{i}\right)^{2}}{\sum_{i=1}^{n}\left(1-a_{i}\right)}-\sum_{i=1}^{n}\left(1-a_{i}\right) . \end{array} $$
      trans (∑ i, ∑ j ∈ Iio i, (a i - a j) ^ 2) / (∑ i, a i)
      · apply le_of_eq
        field_simp
        rw [←hlem]
      trans (∑ i, ∑ j ∈ Iio i, (a i - a j) ^ 2) / ∑ i, (1 - a i)
      · apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · apply sum_le_sum
          intro i _
          apply le_sub_left_of_add_le
          ring_nf
          linarith only [ha₂ (i := i)]
      · apply le_of_eq
        trans (∑ i, ∑ j ∈ Iio i, (1 - a i - (1 - a j)) ^ 2) / ∑ i, (1 - a i)
        · rw [hlem, sub_div]
          field_simp
        · congr
          ext i
          simp
          congr
          ext j
          ring

    -- Next, prove:
    -- $$ \begin{array}{l} \sum_{i=1}^{n} a_{i}-n \sqrt[n]{\prod_{i=1}^{n} a_{i}} \ \geqslant \sum_{i=1}^{n}\left(1-a_{i}\right)-n \sqrt[n]{\prod_{i=1}^{n}\left(1-a_{i}\right)} . \end{array} $$
    have h₂ {a : Fin n → ℝ} (ha : ∀ (i : Fin n), 0 < a i ∧ a i ≤ 1 / 2) {k : ℕ} (hk : k = (univ.filter (fun i : Fin n => a i ≠ (∏ i, a i) ^ (1 / n : ℝ))).card) :
        ∑ i, a i - n * (∏ i, a i) ^ (1 / n : ℝ) ≥ ∑ i, (1 - a i) - n * (∏ i, (1 - a i)) ^ (1 / n : ℝ) := by
      -- Induction on $k$, the number of elements in $a_i$ that differ from the geometric mean.
      induction k using Nat.strongRecOn generalizing a
      rename_i k ih
      by_cases hk0 : k = 0
      · let x := (∏ i, a i) ^ (1 / n : ℝ)
        have hx : x > 0 := by
          simp [x]
          apply rpow_pos_of_pos
          apply prod_pos
          intro i _
          exact (ha i).1
        have hx' : x ≤ 1 := by
          simp [x]
          apply rpow_le_one
          · apply prod_nonneg
            intro i _
            apply le_of_lt (ha i).1
          · apply prod_le_one
            · intro i _
              apply le_of_lt (ha i).1
            · intro i _
              apply le_trans (ha i).2
              norm_num
          · simp
        simp [hk0] at hk
        have hx : ∀ i, a i = x := by
          by_contra h
          simp at h
          obtain ⟨t, ht⟩ := h
          have : {t} ⊆ filter (fun i => ¬a i = (∏ i : Fin n, a i) ^ (↑n : ℝ)⁻¹) univ := by
            simp [x] at ht
            simp [ht]
          apply card_le_card at this
          simp [←hk] at this
        simp [hx]
        apply le_of_eq
        rw [←rpow_natCast, ←rpow_natCast, ←rpow_mul, mul_inv_cancel₀, rpow_one]
        rw [←rpow_mul, mul_inv_cancel₀, rpow_one]
        · ring
        any_goals positivity
        simp [hx']
      · let x := (∏ i, a i) ^ (1 / n : ℝ)
        have hx : x > 0 := by
          simp [x]
          apply rpow_pos_of_pos
          apply prod_pos
          intro i _
          exact (ha i).1
        have hx' : x ≤ 1 := by
          simp [x]
          apply rpow_le_one
          · apply prod_nonneg
            intro i _
            apply le_of_lt (ha i).1
          · apply prod_le_one
            · intro i _
              apply le_of_lt (ha i).1
            · intro i _
              apply le_trans (ha i).2
              norm_num
          · simp
        push_neg at hk0
        let x := (∏ i, a i) ^ (1 / n : ℝ)
        have hx : x > 0 := by
          simp [x]
          apply rpow_pos_of_pos
          apply prod_pos
          intro i _
          exact (ha i).1
        have hx' : x ≤ 1 := by
          simp [x]
          apply rpow_le_one
          · apply prod_nonneg
            intro i _
            apply le_of_lt (ha i).1
          · apply prod_le_one
            · intro i _
              apply le_of_lt (ha i).1
            · intro i _
              apply le_trans (ha i).2
              norm_num
          · simp
        -- Let $a_1$ and $a_2$ be the smallest and largest elements of $a_i$ ($1 \leqslant i \leqslant n$), respectively. Then $a_1 \leqslant x \leqslant a_2$.
        have hne : (univ.image a).Nonempty := by
          use a ⟨0, hn⟩
          simp
        obtain ⟨i, _, hi⟩ := mem_image.mp (max'_mem _ hne)
        obtain ⟨j, _, hj⟩ := mem_image.mp (min'_mem _ hne)
        have hi' : a i > x := by
          by_contra h
          push_neg at h
          have : ∏ i, a i < ∏ _ : Fin n, x := by
            apply prod_lt_prod
            · intro _ _
              apply (ha _).1
            · intro _ _
              apply le_trans ?_ h
              rw [hi]
              apply le_max'
              simp
            · by_contra h'
              simp at h'
              have : ∀ i, a i = x := by
                intro i
                apply le_antisymm ?_ (h' i)
                apply le_trans ?_ h
                rw [hi]
                apply le_max'
                simp
              have : k = 0 := by
                rw [hk]
                simp
                refine filter_eq_empty_iff.mpr ?_
                intro i _
                simp [this i, x]
              exact hk0.elim this
          simp at this
          have : x ^ n > x ^ n := by
            apply lt_of_eq_of_lt ?_ this
            simp [x]
            rw [←rpow_natCast, ←rpow_mul, inv_mul_cancel₀, rpow_one]
            any_goals positivity
            apply prod_nonneg
            intro i _
            apply le_of_lt (ha i).1
          simp at this
        have hj' : a j < x := by
          by_contra h
          push_neg at h
          have : ∏ i, a i > ∏ _ : Fin n, x := by
            apply prod_lt_prod
            · intro _ _
              positivity
            · intro _ _
              apply le_trans h
              rw [hj]
              apply min'_le
              simp
            · use i
          simp at this
          have : x ^ n > x ^ n := by
            apply lt_of_lt_of_eq this
            simp [x]
            rw [←rpow_natCast, ←rpow_mul, inv_mul_cancel₀, rpow_one]
            any_goals positivity
            apply prod_nonneg
            intro i _
            apply le_of_lt (ha i).1
          simp at this
        have : 1 - a i > 0 := by
          simp
          apply lt_of_le_of_lt (ha i).2
          norm_num
        have : 1 - a j > 0 := by
          simp
          apply lt_of_le_of_lt (ha j).2
          norm_num
        have hij : i ≠ j := by
          by_contra h
          rw [h] at hi'
          linarith only [hi', hj']
        have hn' : n ≥ 2 := by
          have : {i, j} ⊆ univ := by simp
          apply card_le_card at this
          simp at this
          apply le_of_eq_of_le ?_ this
          symm
          apply card_eq_two.mpr
          use i, j, hij
        -- Fix $\prod_{i=1}^{n} a_{i}$ and adjust $a_{1}$ and $a_{2}$ to $x$ and $\frac{a_{1} a_{2}}{x}$, respectively. Let:
        -- $$ \begin{array}{l} s=a_{1}+a_{2}-x-\frac{a_{1} a_{2}}{x} \geqslant 0 . \ \text { Then } \Delta f \ =n \sqrt[n]{\prod_{i=3}^{n}\left(1-a_{i}\right)} \cdot \ \quad\left(\sqrt[n]{(1-x)\left(1-\frac{a_{1} a_{2}}{x}\right)}-\sqrt[n]{\left(1-a_{1}\right)\left(1-a_{2}\right)}\right)-2 s . \end{array} $$
        let a' (t : Fin n) := if t = i then x else if t = j then (a i * a j) / x else a t
        let m := (univ.filter (fun i : Fin n => a' i ≠ (∏ i, a i) ^ (1 / n : ℝ))).card
        have hm : m < k := by
          unfold m
          have : univ.filter (fun i : Fin n => a' i ≠ (∏ i, a i) ^ (1 / n : ℝ)) ⊆ univ.filter (fun i : Fin n => a i ≠ (∏ i, a i) ^ (1 / n : ℝ)) \ {i} := by
            intro k hk
            simp at hk ⊢
            by_cases hk' : k = i
            · simp [a', hk', x] at hk
            · simp [hk']
              simp [a', hk'] at hk
              by_cases hk'' : k = j
              · simp [hk'']
                apply ne_of_lt
                apply lt_of_lt_of_eq hj'
                simp [x]
              · simp [a', hk''] at hk
                exact hk
          have : (univ.filter (fun i : Fin n => a' i ≠ (∏ i, a i) ^ (1 / n : ℝ))).card ≤ (univ.filter (fun i : Fin n => a i ≠ (∏ i, a i) ^ (1 / n : ℝ)) \ {i}).card := by
            exact card_le_card this
          apply lt_of_le_of_lt this
          rw [card_sdiff]
          · simp [hk]
            use i
            simp
            apply ne_of_gt
            apply lt_of_eq_of_lt ?_ hi'
            simp [x]
          · simp
            apply ne_of_gt
            apply lt_of_eq_of_lt ?_ hi'
            simp [x]
        have ha' : ∀ (i : Fin n), 0 < a' i ∧ a' i ≤ 1 / 2 := by
          intro i'
          constructor
          · simp [a']
            split_ifs
            · positivity
            · apply div_pos
              · apply mul_pos
                · apply (ha _).1
                · apply (ha _).1
              · positivity
            · apply (ha _).1
          · simp [a']
            split_ifs
            · unfold x
              trans (∏ i : Fin n, 1 / 2) ^ (1 / ↑n : ℝ)
              · gcongr
                · apply prod_nonneg
                  intro i _
                  apply le_of_lt
                  apply (ha _).1
                · intro i _
                  apply le_of_lt
                  apply (ha _).1
                · apply le_trans (ha _).2
                  norm_num
              · simp
                rw [inv_rpow]
                apply le_of_eq
                congr
                rw [←rpow_natCast, ←rpow_mul, mul_inv_cancel₀, rpow_one]
                all_goals positivity
            · trans a i * 1
              · rw [mul_div_assoc]
                apply mul_le_mul_of_nonneg_left
                · apply div_le_one ?_ |>.mpr
                  · apply le_of_lt hj'
                  · positivity
                · apply le_of_lt (ha i).1
              · simp
                apply le_trans (ha i).2
                norm_num
            · apply le_trans (ha i').2
              norm_num
        have hu : univ = univ \ {i, j} ∪ {i, j} := by
          ext x
          simp
          by_cases hi : x = i
          · simp [hi]
          · simp [hi]
            exact ne_or_eq x j
        have hdis : Disjoint (univ \ {i, j}) {i, j} := by simp
        have ha'' : ∏ i : Fin n, a' i = ∏ i, a i := by
          rw [hu, prod_union hdis, prod_union hdis]
          congr 1
          · apply prod_congr rfl
            intro i hi
            simp at hi
            simp [a', hi.1, hi.2]
          · rw [prod_insert, prod_insert]
            · simp [a', Ne.symm hij]
              rw [mul_div_cancel₀]
              positivity
            all_goals simp [hij]
        have hm' : m = #(filter (fun i ↦ a' i ≠ (∏ i : Fin n, a' i) ^ (1 / n : ℝ)) univ) := by
          unfold m
          rw [ha'']
        obtain ih := ih (a := a') m hm ha' hm'
        apply sub_nonneg.mpr at ih
        apply sub_nonneg.mp
        apply le_trans ih
        apply sub_nonpos.mp
        let s := a i + a j - x - (a i * a j) / x
        have hs : s ≥ 0 := by
          unfold s
          field_simp
          apply div_nonneg
          · trans (a i - x) * (x - a j)
            · apply mul_nonneg
              · simp
                apply le_of_lt hi'
              · simp
                apply le_of_lt hj'
            · apply le_of_eq
              ring
          · positivity
        -- Note that:
        -- $$ \begin{aligned} a & \triangleq \sqrt[n]{(1-x)\left(1-\frac{a_{1} a_{2}}{x}\right)} \ & =\sqrt[n]{\left(1-a_{1}\right)\left(1-a_{2}\right)+s} \ & \geqslant \sqrt[n]{\left(1-a_{1}\right)\left(1-a_{2}\right)} \triangleq b . \end{aligned} $$
        let p := ((1 - x) * (1 - (a i * a j) / x)) ^ (1 / n : ℝ)
        let q := ((1 - a i) * (1 - a j)) ^ (1 / n : ℝ)
        trans n * (∏ i ∈ univ \ {i, j}, (1 - a i)) ^ (1 / n : ℝ) * (p - q) - 2 * s
        · apply le_of_eq
          trans  ↑n * (∏ i : Fin n, (1 - a' i)) ^ (1 / ↑n : ℝ) - ↑n * (∏ i : Fin n, a' i) ^ (1 / ↑n : ℝ) -
          (↑n * (∏ i : Fin n, (1 - a i)) ^ (1 / ↑n : ℝ) - ↑n * (∏ i : Fin n, a i) ^ (1 / ↑n : ℝ))
           + (∑ i : Fin n, a' i - (∑ i : Fin n, (1 - a' i)) - (∑ i : Fin n, a i - (∑ i : Fin n, (1 - a i))))
          · ring
          · have : (∑ i : Fin n, a' i - ∑ i : Fin n, (1 - a' i) - (∑ i : Fin n, a i - ∑ i : Fin n, (1 - a i))) = -2 * s := by
              simp
              rw [hu, sum_union hdis, sum_union hdis]
              have h₁ : ∑ x ∈ univ \ {i, j}, a' x = ∑ x ∈ univ \ {i, j}, a x := by
                apply sum_congr rfl
                intro i hi
                simp at hi
                simp [a', hi.1, hi.2]
              rw [h₁]
              ring_nf
              rw [sum_insert, sum_insert]
              simp [a', Ne.symm hij]
              ring_nf
              all_goals
                simp [hij]
            rw [this, ha'']
            congr 1
            simp
            rw [←mul_sub, mul_assoc]
            congr
            rw [mul_sub]
            congr
            · nth_rw 1 [hu]
              rw [prod_union hdis, mul_rpow]
              · congr 2
                · apply prod_congr rfl
                  intro x hx
                  simp at hx
                  congr
                  unfold a'
                  simp [hx.1, hx.2]
                · rw [prod_insert]
                  unfold a'
                  simp [show j ≠ i by exact id (Ne.symm hij)]
                  simp [hij]
                · simp
              · apply prod_nonneg
                intro i hi
                simp at hi
                simp [a', hi]
                apply le_trans (ha i).2
                norm_num
              · apply prod_nonneg
                intro i' hi
                simp at hi
                by_cases hi' : i' = i
                · simp [a', hi']
                  exact hx'
                · simp [hi'] at hi
                  simp [a', hi', Eq.symm hi]
                  rw [hi]
                  trans a i * 1
                  · rw [mul_div_assoc]
                    apply mul_le_mul_of_nonneg_left
                    · apply div_le_one ?_ |>.mpr
                      · apply le_of_lt hj'
                      · positivity
                    · apply le_of_lt (ha i).1
                  · simp
                    apply le_trans (ha i).2
                    norm_num
            · nth_rw 1 [hu]
              rw [prod_union hdis, mul_rpow]
              · congr
                rw [prod_insert]
                any_goals simp
                exact hij
              all_goals
                apply prod_nonneg
                intro i _
                simp
                apply le_trans (ha i).2
                norm_num
            · ring
        · -- Therefore, $\Delta f$:
          -- $$ \begin{array}{l} =n \sqrt[n]{\prod_{i=3}^{n}\left(1-a_{i}\right)} \cdot \ \left(\sqrt[n]{(1-x)\left(1-\frac{a_{1} a_{2}}{x}\right)}-\sqrt[n]{\left(1-a_{1}\right)\left(1-a_{2}\right)}\right)-2 s \ =n \sqrt[n]{\prod_{i=3}^{n}\left(1-a_{i}\right)} \frac{a^{n}-b^{n}}{a^{n-1}+\cdots+b^{n-1}}-2 s \ \leqslant n \sqrt[n]{\left(1-a_{1}\right)^{n-2}} \frac{s}{n b^{n-1}}-2 s \ =\frac{s}{\sqrt[n]{\left(1-a_{1}\right)\left(1-a_{2}\right)^{n-1}}}-2 s \ \leqslant \frac{s}{\frac{1}{2}}-2 s=0 \text {. } \ \end{array} $$
          -- Hence, $\Delta f \leqslant 0$. Adjusting all $a_i$ to $x$, we have $f \geqslant n(1-x)-n x+2 n x-n=0$.
          have hpq : p ≥ q := by
            trans ((1 - a i) * (1 - a j) + s) ^ (1 / n : ℝ)
            · unfold p
              apply le_of_eq
              congr
              unfold s
              rw [sub_mul, mul_sub, mul_sub]
              ring_nf
              rw [mul_inv_cancel_right₀]
              positivity
            · unfold q
              gcongr
              simp
              exact hs
          have h : p - q ≤ s / (n * q ^ (n - 1)) := by
            trans (p ^ n - q ^ n) / (n * q ^ (n - 1))
            · rw [sub_div]
              have : (p - q) / q ≤ (p ^ n / (↑n * q ^ (n - 1)) - q ^ n / (↑n * q ^ (n - 1))) / q := by
                trans p / q - 1
                · apply le_of_eq; field_simp
                trans 1 / n * ((p / q) ^ n - 1)
                · trans 1 / ↑n * (n * (p / q - 1))
                  · apply le_of_eq
                    field_simp
                  · gcongr
                    trans (1 + (p / q - 1)) ^ n - 1
                    · apply le_sub_left_of_add_le
                      refine one_add_mul_le_pow ?_ n
                      trans 0
                      · simp
                      · simp
                        refine (one_le_div₀ ?_).mpr hpq
                        unfold q
                        positivity
                    · simp
                · apply le_of_eq
                  field_simp
                  left
                  nth_rw 4 [show n = n - 1 + 1 by rw [Nat.sub_add_cancel hn]]
                  rw [pow_add, pow_one]
                  ring
              apply div_le_div_iff_of_pos_right ?_ |>.mp this
              unfold q
              positivity
            · gcongr
              unfold p q s
              rw [←rpow_natCast, ←rpow_natCast, ←rpow_mul, ←rpow_mul]
              rw [div_mul_cancel₀, rpow_one, rpow_one]
              apply le_of_eq
              rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, mul_div_cancel₀]
              ring
              any_goals positivity
              apply mul_nonneg
              · simp [hx']
              · simp
                trans a i * 1
                · rw [mul_div_assoc]
                  apply mul_le_mul_of_nonneg_left
                  · apply div_le_one ?_ |>.mpr
                    · apply le_of_lt hj'
                    · positivity
                  · apply le_of_lt (ha i).1
                · simp
                  apply le_trans (ha i).2
                  norm_num
          trans n * ((1 - a j) ^ (n - 2)) ^ (1 / n : ℝ) * (s / (n * q ^ (n - 1))) - 2 * s
          · gcongr
            · exact sub_nonneg_of_le hpq
            · apply prod_nonneg
              intro i _
              simp
              apply le_trans (ha i).2
              norm_num
            · trans ∏ t ∈ univ \ {i, j}, (1 - a j)
              · apply prod_le_prod
                · intro i _
                  simp
                  apply le_trans (ha i).2
                  norm_num
                · intro i _
                  rw [hj]
                  apply sub_le_sub (le_refl _)
                  apply min'_le
                  simp
              · apply le_of_eq
                simp
                congr
                rw [card_sdiff]
                simp; congr
                · apply card_eq_two.mpr
                  use i, j, hij
                · simp
          trans s / ((1 - a i) ^ (n - 1) * (1 - a j)) ^ (1 / n : ℝ) - 2 * s
          · gcongr
            apply le_of_eq
            field_simp
            unfold q
            rw [mul_rpow, mul_rpow, mul_pow]
            have : n - 1 = n - 2 + 1 := by
              simp
              rw [Nat.sub_add_cancel hn']
            nth_rw 3 [this]
            rw [pow_add, pow_one]
            rw [←rpow_natCast, ←rpow_natCast, ←rpow_natCast, ←rpow_natCast]
            rw [←rpow_mul, ←rpow_mul, ←rpow_mul, ←rpow_mul]
            · ring_nf
            all_goals positivity
          trans s / (1 / 2) - 2 * s
          · gcongr
            trans ((1 - (1 / 2)) ^ (n - 1) * (1 - (1 / 2))) ^ (1 / ↑n : ℝ)
            · rw [←rpow_natCast _ (n - 1), ←rpow_add_one, ←rpow_mul, Nat.cast_sub hn]
              · apply le_of_eq
                norm_num
                field_simp
              all_goals positivity
            · gcongr
              · exact (ha i).2
              · exact (ha j).2
          · apply le_of_eq
            ring

    -- In conclusion, the original problem is proved.
    exact add_le_add h₁ (h₂ ha (k := #(filter (fun i => a i ≠ (∏ i, a i) ^ (1 / ↑n : ℝ)) univ)) rfl)
