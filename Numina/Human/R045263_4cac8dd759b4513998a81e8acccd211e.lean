import Mathlib

open Real Finset

theorem algebra_120276 {n : ℕ} (hn : 2 ≤ n) :
    IsLeast {t | ∃ x : ℕ → ℝ, (∀ i ∈ range n, 1 / n ≤ x i) ∧ (∑ i ∈ range n, (x i) ^ 2) = 1
    ∧ t = ∏ i ∈ range n, x i} (√(n ^ 2 - n + 1) / n ^ n) ∧ IsGreatest {t | ∃ x : ℕ → ℝ,
    (∀ i ∈ range n, 1 / n ≤ x i) ∧ (∑ i ∈ range n, (x i) ^ 2) = 1 ∧ t = ∏ i ∈ range n, x i} (1 / √n ^ n) := by
  have aux1 : 0 ≤ (n : ℝ) ^ 2 - n + 1 := by
    rw [sub_add_eq_add_sub, sub_nonneg, pow_two]; norm_cast
    linarith only [Nat.le_mul_self n]
  have aux3 : ∀ x : ℕ → ℝ, (∀ i ∈ range n, 1 / n ≤ x i) → (∑ i ∈ range n, (x i) ^ 2) = 1 →
  1 + #(filter (fun i => x i = 1 / n) (range n)) ≤ n := by
    intro x hx1 hx2; have : #(filter (fun i => x i = 1 / n) (range n)) ≤ n := by
      nth_rw 4 [show n = #(range n) by simp]
      apply card_filter_le
    by_contra!; replace this : #(filter (fun i => x i = 1 / n) (range n)) = n := by omega
    nth_rw 4 [show n = #(range n) by simp] at this
    rw [card_filter_eq_iff] at this
    suffices : ∑ i ∈ range n, x i ^ 2 = ∑ i ∈ range n, 1 / (n : ℝ) ^ 2
    · simp [this] at hx2; field_simp at hx2
      norm_cast at hx2; symm at hx2
      rw [pow_two, Nat.mul_eq_left] at hx2
      all_goals omega
    apply sum_congr rfl; intros; rw [this]; ring
    assumption
  constructor
  · simp [IsLeast, lowerBounds]; constructor
    · let x : ℕ → ℝ := fun i => if i < n - 1 then 1 / n else √(n ^ 2 - n + 1) / n
      use x; split_ands
      · intro i _; dsimp [x]; split; simp
        rw [← one_div, div_le_div_iff_of_pos_right, le_sqrt]; simp
        norm_cast; rw [pow_two]; exact Nat.le_mul_self n
        all_goals positivity
      · rw [show n = n-1+1 by omega]; simp [sum_range_succ, x]
        repeat rw [sum_ite_of_true]
        simp [← one_div]; rw [Nat.cast_sub]; push_cast
        rw [mul_one_div, div_pow]
        rw [sq_sqrt, div_add_div_same]; field_simp
        exact aux1; omega; simp
      nth_rw 5 [show n = n-1+1 by omega]
      simp [prod_range_succ, x]; rw [prod_ite_of_true]
      simp [← one_div]; field_simp; left
      rw [← pow_succ, Nat.sub_add_cancel]; omega
      any_goals simp
    intro t x hx1 hx2 ht; rw [ht]; clear t ht
    set m' := n - 1 - #{i ∈ range n | x i = 1 / n} with hm
    have mle : m' ≤ n - 1 := by omega
    generalize m' = m at mle hm; clear m'; revert hm mle x
    induction m with
    | zero =>
      intro x hx1 hx2 _ hc; symm at hc
      obtain ⟨k, ⟨hk1, hk2, hk3⟩⟩ : ∃ k ∈ range n, x k = √(n ^ 2 - n + 1) / n ∧
      ∀ i ∈ ((range n) \ {k}), x i = 1 / n := by
        suffices : #(filter (fun i => ¬ x i = 1 / n) (range n)) = 1
        · rw [card_eq_one] at this; rcases this with ⟨k, hk⟩
          simp [Finset.ext_iff] at hk; use k
          have kmem : k ∈ range n := by
            specialize hk k; simp; exact (hk.mpr rfl).left
          replace hk : ∀ i ∈ range n \ {k}, x i = 1 / n := by
            simp; intro i hi _; by_contra!
            have := (hk i).mp ⟨hi, this⟩; contradiction
          split_ands; exact kmem
          · rw [sum_eq_sum_diff_singleton_add kmem] at hx2
            suffices : ∑ x_1 ∈ range n \ {k}, x x_1 ^ 2 = ∑ x_1 ∈ range n \ {k}, 1 / (n : ℝ) ^ 2
            · simp [this] at hx2; rw [card_sdiff] at hx2
              simp [← one_div] at hx2; rw [Nat.cast_sub] at hx2; push_cast at hx2
              rw [← eq_sub_iff_add_eq', mul_one_div, one_sub_div] at hx2
              rw [← sq_eq_sq₀, hx2, div_pow, sq_sqrt]; ring; exact aux1
              · specialize hx1 k (by simp at kmem; exact kmem)
                apply le_trans _ hx1; positivity
              any_goals positivity
              omega; simp; simp at kmem; exact kmem
            apply sum_congr rfl; intro i hi
            specialize hk i hi; rw [hk]; ring
          exact hk
        rw [filter_not, card_sdiff]; simp [← one_div]
        rw [Nat.sub_sub] at hc; apply Nat.eq_add_of_sub_eq at hc
        nth_rw 1 [hc]; omega
        · exact aux3 x (by simp; intro i hi; exact hx1 i hi) hx2
        apply filter_subset
      rw [prod_eq_prod_diff_singleton_mul hk1, prod_congr rfl hk3, hk2]
      simp; rw [card_sdiff]; simp; field_simp; rw [← pow_succ]
      rw [Nat.sub_add_cancel]; omega; simp; simp at hk1
      exact hk1
    | succ m ihm =>
      intro x hx1 hx2 hm1 hm2
      have xpos : ∀ i < n, 0 < x i := by
        intro i hi; specialize hx1 i hi
        apply lt_of_lt_of_le _ hx1; positivity
      rw [Nat.sub_sub] at hm2; nth_rw 2 [add_comm] at hm2
      rw [← Nat.sub_sub] at hm2; nth_rw 1 [show n = #(range n) by simp] at hm2
      rw [← card_sdiff, ← filter_not] at hm2; symm at hm2
      apply Nat.eq_add_of_sub_eq at hm2; rw [show m+1+1 = m+2 by ring] at hm2
      obtain ⟨s, ⟨subs, sc⟩⟩ := exists_subset_card_eq (show 2≤#(filter (fun a => ¬x a = 1 / ↑n) (range n)) by rw [hm2]; simp)
      rw [card_eq_two] at sc; rcases sc with ⟨i, j, ⟨inej, hij⟩⟩
      simp [hij, subset_iff, ← one_div, and_assoc] at subs
      rcases subs with ⟨ilt, xine, jlt, xjne⟩
      have aux2 : 0 ≤ x i ^ 2 + x j ^ 2 - ((n : ℝ) ^ 2)⁻¹ := by
        rw [← add_sub]; suffices : 0 ≤ (x j ^ 2 - ((n : ℝ) ^ 2)⁻¹)
        · specialize xpos i ilt; positivity
        rw [sub_nonneg, ← inv_pow, pow_le_pow_iff_left₀]
        apply hx1; exact jlt; any_goals positivity
        specialize xpos j jlt; positivity
      let x' : ℕ → ℝ := fun t => if t = i then 1 / n else if t = j then √(x i ^ 2 + x j ^ 2 - 1 / n ^ 2) else x t
      have prodle : ∏ i ∈ range n, x' i ≤ ∏ i ∈ range n, x i := by
        have : i ∈ range n := by simp; exact ilt
        rw [prod_eq_prod_diff_singleton_mul this, prod_eq_prod_diff_singleton_mul this]
        replace this : j ∈ range n \ {i} := by simp; exact ⟨jlt, by omega⟩
        rw [prod_eq_prod_diff_singleton_mul this, prod_eq_prod_diff_singleton_mul this]
        simp [x']; rw [ite_cond_eq_false, prod_ite_of_false]
        rw [prod_ite_of_false, mul_assoc, mul_assoc]
        rw [mul_le_mul_left, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
        rw [mul_pow, mul_pow, sq_sqrt, ← sub_nonneg]; calc
          _ ≤ (x i ^ 2 - (n : ℝ)⁻¹ ^ 2) * (x j ^ 2 - (n : ℝ)⁻¹ ^ 2) := by
            apply mul_nonneg; all_goals rw [sub_nonneg]
            all_goals rw [pow_le_pow_iff_left₀]; apply hx1
            exact ilt; any_goals positivity
            · specialize xpos i ilt; positivity
            exact jlt; specialize xpos j jlt; positivity
          _ = _ := by rw [← inv_pow]; ring
        · exact aux2
        · positivity
        · apply mul_nonneg; specialize xpos j jlt; positivity
          specialize xpos i ilt; positivity
        · apply prod_pos; intro k hk; simp [and_assoc] at hk
          apply xpos; exact hk.left
        · intro k hk; simp [and_assoc] at hk
          exact hk.right.right
        · intro k hk; simp [and_assoc] at hk
          exact hk.right.left
        simp; intro h; simp [h] at inej
      have hx'1 : ∀ i < n, (↑n)⁻¹ ≤ x' i := by
        intro k hk; simp [x']; split_ifs; rfl
        · rw [le_sqrt, ← inv_pow, le_sub_iff_add_le]; apply add_le_add
          any_goals rw [pow_le_pow_iff_left₀]; apply hx1
          any_goals assumption
          any_goals positivity
          · specialize xpos i ilt; positivity
          · specialize xpos j jlt; positivity
        exact hx1 k hk
      have hx'2 : ∑ i ∈ range n, x' i ^ 2 = 1 := by
        have : i ∈ range n := by simp; exact ilt
        rw [sum_eq_sum_diff_singleton_add this]
        have this' : j ∈ range n \ {i} := by simp; exact ⟨jlt, by omega⟩
        rw [sum_eq_sum_diff_singleton_add this']
        simp [x']; rw [ite_cond_eq_false, sum_ite_of_false]
        rw [sum_ite_of_false, sq_sqrt, add_assoc, sub_add_cancel]
        nth_rw 2 [add_comm]; rw [← add_assoc]
        rw [← sum_eq_sum_diff_singleton_add this']
        rw [← sum_eq_sum_diff_singleton_add this]; exact hx2
        · exact aux2
        · intro k hk; simp [and_assoc] at hk
          exact hk.right.right
        · intro k hk; simp [and_assoc] at hk
          exact hk.right.left
        simp; intro h; simp [h] at inej
      apply le_trans _ prodle; apply ihm; any_goals assumption
      · omega
      · rw [Nat.sub_sub, add_comm]
        rw [← Nat.sub_sub]; nth_rw 1 [show n = #(range n) by simp]
        rw [← card_sdiff, ← filter_not]; symm
        rw [Nat.sub_eq_iff_eq_add, show m+1 = m+2-1 by omega, ← hm2]
        suffices : (filter (fun a => ¬x a = 1 / ↑n) (range n)) =
        (filter (fun a => ¬x' a = 1 / ↑n) (range n)) ∪ {i}
        · rw [this, card_union_of_disjoint]; simp
          simp [x']
        simp [Finset.ext_iff, x']; intro k; constructor
        · rintro ⟨klt, xkne⟩; by_cases h : k = i
          · right; exact h
          left; split_ands; exact klt; exact h; split_ifs with h'
          · suffices : (n : ℝ)⁻¹ < √(x i ^ 2 + x j ^ 2 - ((n : ℝ) ^ 2)⁻¹)
            · intro h; simp [h] at this
            rw [lt_sqrt, ← inv_pow, lt_sub_iff_add_lt]
            apply add_lt_add
            · rw [pow_lt_pow_iff_left₀, lt_iff_le_and_ne]
              constructor; apply hx1; exact ilt
              intro h; simp [← h] at xine
              any_goals positivity
              specialize xpos i ilt; positivity
            rw [pow_lt_pow_iff_left₀, lt_iff_le_and_ne]
            constructor; apply hx1; exact jlt
            intro h; simp [← h] at xjne
            any_goals positivity
            specialize xpos j jlt; positivity
          exact xkne
        · split_ifs with h'; intro h; rcases h with ⟨klt, knei, hne⟩|h
          · constructor; exact klt; rw [h', ← one_div]; exact xjne
          · rw [← h'] at inej; rw [h] at inej; contradiction
          intro h; rcases h with ⟨klt, knei, hne⟩|h
          · constructor; exact klt; exact hne
          constructor; rw [h]; exact ilt
          rw [h, ← one_div]; exact xine
        · rw [filter_not, card_sdiff]; simp [← one_div]
          specialize aux3 x' (by simp; intro k hk; exact hx'1 k hk) hx'2
          omega; apply filter_subset
        apply filter_subset
      rw [filter_not, card_sdiff]; simp [← one_div]
      specialize aux3 x (by simp; intro k hk; exact hx1 k hk) hx2
      omega; all_goals apply filter_subset
  simp [IsGreatest, upperBounds]; constructor
  · let x : ℕ → ℝ := fun _ => 1 / √n; use x; split_ands
    · intros; simp [x]; rw [inv_le_inv₀, sqrt_le_iff]
      simp [pow_two]; norm_cast; apply Nat.le_mul_self
      any_goals positivity
    · simp [x]; field_simp
    simp [x]
  intro t x hx1 hx2 ht; rw [ht]; clear t ht
  let w : ℕ → ℝ := fun _ => 1 / n; let z : ℕ → ℝ := fun i => x i ^ 2
  have hw1 : ∀ i ∈ range n, 0 ≤ w i := by simp [w]
  have hw2 : 0 < ∑ i ∈ range n, w i := by simp [w]; field_simp
  have hz : ∀ i ∈ range n, 0 ≤ z i := by simp [z]; intros; apply sq_nonneg
  have AMGM := geom_mean_le_arith_mean (range n) w z hw1 hw2 hz
  simp [w, z] at AMGM; field_simp at AMGM
  rw [← sum_div, hx2, ← pow_le_pow_iff_left₀ _ _ (show n≠0 by omega)] at AMGM
  rw [finset_prod_rpow, ← rpow_natCast, ← rpow_mul] at AMGM
  field_simp at AMGM; rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by omega)]
  rw [← prod_pow, inv_pow, ← pow_mul, mul_comm, pow_mul]
  rw [sq_sqrt, ← one_div]; exact AMGM
  any_goals positivity
  apply prod_nonneg; simp; intro i hi; specialize hx1 i hi
  apply le_trans _ hx1; positivity
  intros; apply sq_nonneg
