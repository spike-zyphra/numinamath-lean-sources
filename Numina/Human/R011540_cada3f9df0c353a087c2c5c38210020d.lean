import Mathlib

theorem Nat.div_eq_zero_iff_lt : ∀ {k x : ℕ}, 0 < k → (x / k = 0 ↔ x < k) := sorry

open Finset Classical

/-Let $M$ be the set of all positive integers that do not contain the digit $9$ (base $10$). If $x_1, \ldots , x_n$ are arbitrary but distinct elements in $M$, prove that
\[\sum_{j=1}^n \frac{1}{x_j} < 80 .\]-/
theorem number_theory_34073 {M : Set ℕ} {x : ℕ → ℕ} {n : ℕ} {npos : 0 < n}
    (hM : M = {m | 0 < m ∧ 9 ∉ Nat.digits 10 m}) (hx : Set.MapsTo x (range n) M)
    (xinj : Set.InjOn x (range n)) : ∑ i ∈ range n, (1 : ℚ) / x i < 80 := by
-- Prove that $x_i$ are positive for $i < n$
  have xpos : ∀ i < n, 0 < x i := by
    intro i hi; simp [Set.MapsTo, hM] at hx
    specialize hx hi; exact hx.left
-- Take $r$ to be the largest among all $x_i$ with $i < n$
  have imgne : (image x (range n)).Nonempty := by
    use x 0; simp; use 0
  let r := (image x (range n)).max' imgne
-- Take $R$ to be the smallest power of $10$ larger than $r$, prove that $x_i < R$ for all $i < n$
  let R := 10 ^ (Nat.log 10 r + 1)
  have imgsb : image x (range n) ⊆ range R := by
    simp [subset_iff, R]; intro i hi; calc
      _ ≤ r := by
        apply le_max'; rw [mem_image]; use i
        simp; exact hi
      _ < _ := by
        rw [Nat.lt_pow_iff_log_lt]; any_goals simp
        dsimp [r]; have := max'_mem _ imgne
        rw [mem_image] at this; rcases this with ⟨l, hl⟩
        rw [mem_range] at hl; specialize xpos l hl.left
        omega
  calc
  -- Enlarge the range of the summation to all members of $M$ less than $R$
    _ ≤ ∑ i ∈ range R with i ∈ M, (1 : ℚ) / i := by
      rw [← sum_image]; nth_rw 2 [← sum_image]
      apply sum_le_sum_of_subset_of_nonneg
      · simp [subset_iff]; intro i hi
        simp [subset_iff] at imgsb; simp [Set.MapsTo] at hx
        exact ⟨imgsb i hi, hx hi⟩
      · simp; intro q _ _ _ hq _; simp [← hq]
      · intros; qify; assumption
      intros; apply xinj; any_goals assumption
      qify; assumption
  -- Generalize the power of $10$ to any positive integer $p$
    _ < _ := by
      dsimp [R]; have ppos : 0 < Nat.log 10 r + 1 := by simp
      generalize Nat.log 10 r + 1 = p at ppos
      clear * - hM ppos; rw [range_eq_Ico]; calc
      -- Prove by induction that we can split the sum according to digits of numbers
        _ = ∑ j ∈ range p, ∑ i ∈ Ico (10 ^ j) (10 ^ (j + 1)) with i ∈ M, (1 : ℚ) / i := by
          induction p with
          | zero => simp at ppos
          | succ p ih =>
            by_cases h : p = 0
            · simp [h]; congr 1; simp [Finset.ext_iff]
              intro a ha _; simp [hM] at ha; omega
            specialize ih (by omega)
            rw [← Ico_union_Ico_eq_Ico (show 0≤10^p by simp), filter_union]
            rw [sum_union, ih, sum_range_succ]
            · apply disjoint_filter_filter
              exact Ico_disjoint_Ico_consecutive 0 (10 ^ p) (10 ^ (p + 1))
            gcongr; all_goals simp
        _ ≤ ∑ j ∈ range p, ∑ i ∈ Ico (10 ^ j) (10 ^ (j + 1)) with i ∈ M, (1 : ℚ) / 10 ^ j := by
          gcongr with j hj i hi; simp at hi
          norm_cast; exact hi.left.left
        _ = ∑ j ∈ range p, (8 : ℚ) * 9 ^ j * (1 / 10 ^ j) := by
          simp; apply sum_congr rfl
          intro m _; congr; norm_cast
        -- Compute the cardinality of elements of $M$ with $i$ digits by induction
          clear *- hM; induction m with
            | zero =>
              simp [hM]; suffices : {i ∈ Ico 1 10 | 0 < i ∧ 9 ∉ Nat.digits 10 i}
              = Icc 1 8
              · simp [this]
              simp [Finset.ext_iff]; intro i; constructor
              · rintro ⟨ibd, ipos, hi⟩; rw [Nat.digits_of_lt] at hi
                simp at hi; all_goals omega
              rintro ⟨ige, ile⟩; rw [Nat.digits_of_lt]
              simp; all_goals omega
            | succ m ih =>
              let f : ℕ × ℕ → ℕ := fun (a, b) => 10 * a + b
              have fimg : image f ({i ∈ Ico (10 ^ m) (10 ^ (m + 1)) | i ∈ M} ×ˢ range 9) =
              {i ∈ Ico (10 ^ (m + 1)) (10 ^ (m + 1 + 1)) | i ∈ M} := by
                simp [Finset.ext_iff, f, and_assoc]
                intro s; constructor
                · rintro ⟨a, age, alt, amem, b, blt, hs⟩; rw [← hs]
                  simp [hM] at amem; constructor; omega
                  simp [hM]; split_ands; omega
                  · left; exact amem.left
                  rw [Nat.digits_eq_cons_digits_div, Nat.mul_add_mod]
                  rw [Nat.mul_add_div, (Nat.div_eq_zero_iff_lt _).mpr, add_zero]
                  simp; constructor; omega
                  exact amem.right
                  all_goals omega
                rintro ⟨sbd, smem⟩; simp [hM] at smem
                rw [Nat.digits_eq_cons_digits_div] at smem
                simp at smem; use s / 10
                split_ands; any_goals omega
                · simp [hM]; constructor; omega
                  exact smem.right.right.right
                use s % 10; omega
              have finj : Set.InjOn f ((Set.univ) ×ˢ range 10) := by
                rintro ⟨⟩; simp [f]; intros; omega
              rw [← fimg, card_image_of_injOn]
              simp [ih]; ring
              apply finj.mono; simp [Set.subset_def]
              intros; omega
      -- Compute the geometric sum to finish the goal
        _ = (8 : ℚ) * ∑ j ∈ range p, (9 / 10) ^ j := by
          rw [mul_sum]; apply sum_congr rfl
          intros; rw [div_pow]; ring
        _ < _ := by
          rw [geom_sum_eq, ← neg_div_neg_eq]
          rw [show (80:ℚ) = 8*(-(0-1) / -(9/10-1)) by norm_num]
          gcongr; positivity; norm_num