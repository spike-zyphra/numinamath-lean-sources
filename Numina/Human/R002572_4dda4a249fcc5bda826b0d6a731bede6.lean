import Mathlib

open Finset

/- Let $T = \{9^k : k ~ \mbox{is an integer}, 0 \le k \le 4000\}$. Given that $9^{4000}_{}$ has 3817 [digits](https://artofproblemsolving.com/wiki/index.php/Digit) and that its first (leftmost) digit is 9, how many [elements](https://artofproblemsolving.com/wiki/index.php/Element) of $T_{}^{}$ have 9 as their leftmost digit? -/
theorem number_theory_95611 {T : Set ℕ} (hT : T = {x | ∃ k : ℕ, 0 ≤ k ∧ k ≤ 4000 ∧ x = 9 ^ k})
    (hlen : (Nat.digits 10 (9 ^ 4000)).length = 3817) :
    {x ∈ T | (Nat.digits 10 x).getLastI = 9}.ncard = 184 := by
  -- Define S = {9 ^ k | k ∈ [0, 4001)}.
  set S : Finset ℕ := (range 4001).map ⟨fun k => 9 ^ k, fun i j => by simp⟩
  -- Define U(n) = {x ∈ S | Nat.log 10 x = n}.
  -- U(n) = numbers in S which have exactly (n + 1) digits.
  set U : ℕ → Finset ℕ := fun n => S.filter (fun x => Nat.log 10 x = n)
  -- Define I = [0, 3817).
  set I := range 3817
  -- Define a predicate p(x) which holds for x when the first (leftmost) digit of x is 9.
  set p : ℕ → Prop := fun x => (Nat.digits 10 x).getLastI = 9
  rw [Nat.digits_len _ _ (by norm_num) (by positivity)] at hlen
  -- It is easy to show that T from the theorem statement is equal to S.
  have hTS : T = S := by
    ext x
    simp [hT, S, show ∀ x, x < 4001 ↔ x ≤ 4000 by omega, show ∀ a, x = a ↔ a = x by omega]
  -- All sets U(n) are pairwise disjoint.
  have hU_disj {K : Set ℕ} : K.PairwiseDisjoint U := by
    simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun]
    intro i hi j hj hij
    rw [disjoint_iff_inter_eq_empty]
    ext x
    simp [U]
    omega
  -- S is a union of U(n) for n ∈ I.
  have hSU : S = I.biUnion U := by
    ext x
    simp [S, I, U]
    intro k hk heq
    -- It is enough to show that x ∈ S implies Nat.log 10 x ∈ I or Nat.log 10 x < 3817.
    -- We know that Nat.log 10 (9 ^ 4000) + 1 = 3817 and x ∈ S ↔ x = 9 ^ k with k ≤ 4000.
    rw [← heq, ← hlen]
    apply Nat.lt_add_one_of_le
    -- Nat.log 10 is monotone so x ≤ 9 ^ 4000 implies Nat.log 10 x ≤ Nat.log 10 (9 ^ 4000) = 3816.
    apply Nat.log_mono_right
    apply Nat.pow_le_pow_right (by norm_num) (by omega)
  -- Prove that any non-zero number x can be written in the following form:
  -- x = d * 10^k + r with 0 < d < 10, r < 10^k, and k = Nat.log 10 x.
  have hfirst {x} (hx : x ≠ 0) : ∃ k d r, k = Nat.log 10 x ∧ x = d * 10 ^ k + r ∧ 0 < d ∧ d < 10 ∧ r < 10 ^ k := by
    use Nat.log 10 x, x / 10 ^ Nat.log 10 x, x % 10 ^ Nat.log 10 x
    simp_rw [mul_comm, Nat.div_add_mod, true_and]
    constructorm* _ ∧ _
    · simp only [Nat.div_pos_iff, Nat.ofNat_pos, pow_pos, true_and]
      apply Nat.pow_log_le_self _ hx
    · rw [Nat.div_lt_iff_lt_mul (by positivity)]
      have := @Nat.lt_pow_succ_log_self 10 (by norm_num) x
      rwa [pow_succ, mul_comm] at this
    · apply Nat.mod_lt
      positivity
  -- Prove that the first digit of x = d * 10^k + r with 0 < d < 10 and r < 10^k is d.
  have hlast {x d k r : ℕ} (hx : x = d * 10 ^ k + r) (hd1 : 0 < d) (hd2 : d < 10) (hr : r < 10 ^ k) : (Nat.digits 10 x).getLastI = d := by
    -- Proof by induction on k.
    induction k generalizing x d r with
    | zero =>
      -- If k = 0 then r < 1 implies r = 0 and x = d. So the first digit of x is d.
      simp [hx, show r = 0 by omega, Nat.digits_of_lt 10 d (by omega) hd2, List.getLastI]
    | succ k ih =>
      -- Consider x = d * 10^(k + 1) + r with r < 10^(k + 1).
      -- We have x / 10 = d * 10^k + r / 10 with r / 10 < 10^k.
      have eq : x / 10 = d * 10 ^ k + r / 10 := by
        rw [hx, pow_add, pow_one, ← mul_assoc, mul_comm _ 10, Nat.mul_add_div (by norm_num)]
      -- Apply the induction hypothesis to x / 10 and get d = the first digit of x / 10.
      -- It is left to show that the first digit of x is equal to the first digit of x / 10.
      rw [← ih eq hd1 hd2 (by omega)]
      -- x / 10 ≠ 0 because x ≥ 10.
      have h0 : x / 10 ≠ 0 := by
        rw [eq]
        suffices d * 10 ^ k ≠ 0 by omega
        rw [Nat.mul_ne_zero_iff]
        omega
      -- We have x = (x / 10) * 10 + x % 10 and so the first digit of x is equal
      -- to the first digit of (x / 10) (we just need to show that the list of digits
      -- of x / 10 is not empty).
      nth_rw 1 [← Nat.div_add_mod x 10, add_comm, Nat.digits_add _ (by norm_num)]
      · have hn : Nat.digits 10 (x / 10) ≠ [] := by
          rw [Nat.digits_ne_nil_iff_ne_zero]
          exact h0
        generalize Nat.digits 10 (x / 10) = l at hn ⊢
        cases l with
        | nil => contradiction
        | cons h t => simp [List.getLastI_eq_getLast?]
      · apply Nat.mod_lt _ (by norm_num)
      · right; exact h0
  -- If x ∈ U(n) then x ≠ 0 (because x ∈ U(n) implies x = 9^k for some k).
  have hU0 {n x} (hx : x ∈ U n) : x ≠ 0 := by
    suffices x ∈ S by
      simp [S] at this
      have ⟨k, hk⟩ := this
      rw [← hk.2]
      positivity
    apply mem_of_subset _ hx
    simp only [Nat.reduceLeDiff, filter_subset, U]
  -- For any n, there exists x such that U(n) ⊆ {x, 9 * x}.
  have hU n : ∃ x, U n ⊆ {x, 9 * x} := by
    -- If U(n) = ∅ then U(n) ⊆ {0, 9 * 0}.
    by_cases h : U n = ∅
    · use 0; simp [h]
    simp_rw [← nonempty_iff_ne_empty] at h
    -- If U(n) ≠ ∅ then let x be the minimum element of U(n).
    have ⟨x, hmin⟩ := min_of_nonempty h
    have hx := mem_of_min hmin
    -- Show that U(n) ⊆ {x, 9 * x} for x = U(n).min.
    use x
    -- It is enough to show that for any y ∈ U(n), y = x or y = 9 * x.
    intro y hy
    simp only [mem_insert, mem_singleton]
    -- Consider two cases: y = x and y ≠ x.
    by_cases hyx : y = x
    · left; exact hyx
    -- If y ≠ x then x < y (because x is the minimum).
    replace hyx : x < y := by
      suffices x ≤ y by omega
      exact min_le_of_eq hy hmin
    -- Show that y = 9 * x.
    right
    simp [U, S] at hx hy
    -- We have Nat.log 10 x = Nat.log 10 y = n, x = 9^i, y = 9^j.
    replace ⟨⟨i, hi, hix⟩, hx⟩ := hx
    replace ⟨⟨j, hj, hjy⟩, hy⟩ := hy
    -- x < y implies i < j.
    have hij : i < j := by
      rwa [← Nat.pow_lt_pow_iff_right (show 1 < 9 by norm_num), hix, hjy]
    -- Consider two cases: j = i + 1 or i + 2 ≤ j.
    cases' show j = i + 1 ∨ i + 2 ≤ j by omega with hj hj
    -- If j = i + 1 then y = 9^(i + 1) = 9^i * 9 = 9 * x.
    · rw [← hix, ← hjy, hj, pow_succ, mul_comm]
    -- Show that the case i + 2 ≤ j is impossible by showing that n < Nat.log 10 y.
    suffices n < Nat.log 10 y by linarith
    calc
      -- We have n < Nat.log 10 (9^i * 10) (because Nat.log 10 (9^i * 10) = Nat.log 10 x + 1).
      n < Nat.log 10 (9 ^ i * 10) := by
          rw [Nat.log_mul_base (by norm_num) (by positivity), hix, hx]
          linarith
      -- Nat.log 10 (9^i * 10) ≤ Nat.log 10 (9^(i + 2)) because 10 ≤ 9^2 = 81.
      _ ≤ Nat.log 10 (9 ^ (i + 2)) := by
          apply Nat.log_mono_right
          ring_nf
          omega
      -- Nat.log 10 (9^(i + 2)) ≤ Nat.log 10 y (because 9^(i+2) ≤ 9^j = y).
      _ ≤ Nat.log 10 y := by
          apply Nat.log_mono_right
          rw [← hjy]
          apply Nat.pow_le_pow_right (by norm_num) hj
  -- Show that #U(n) ≤ 1 implies that U(n) has no elements with the first digit equal to 9.
  have hU1 {n} (h : (U n).card ≤ 1) : ((U n).filter p).card = 0 := by
    cases' show (U n).card = 0 ∨ (U n).card = 1 by omega with h h
    -- If #U(n) = 0 then U(n) = ∅ so it has no elements at all.
    · simp only [card_eq_zero] at h
      simp only [h, filter_empty, card_empty]
    -- If #U(n) = 1 then there exists x such that U(n) = {x}.
    rw [card_eq_one] at h
    have ⟨x, hUx⟩ := h
    have hxU : x ∈ U n := by simp only [hUx, mem_singleton]
    have hx0 := hU0 hxU
    simp only [Nat.reduceLeDiff, hUx, card_eq_zero, p]
    -- We need to show that the first digit of x is not 9.
    ext y
    simp
    intro hy
    subst y
    -- Write x as d * 10^k + r with 0 < d < 10 and r < 10^k.
    have ⟨k, d, r, hk, hx, hd1, hd2, hr⟩ := hfirst hx0
    -- The first digit of x is d.
    rw [hlast hx hd1 hd2 hr]
    -- Consider two cases: d < 9 and d = 9.
    cases' show d < 9 ∨ d = 9 by omega with hd hd
    -- If d < 9 then the first digit of x is not 9.
    · linarith
    -- Suppose that d = 9 and show that x / 9 ∈ U(n).
    -- x / 9 ∈ U(n) contradicts the assumption #U(n) = 1.
    suffices hy : x / 9 ∈ U n by
      simp [hUx] at hy
      omega
    -- x ∈ U(n) so x = 9^i for some i < 4001 and Nat.log 10 x = n.
    simp [U, S] at hxU ⊢
    have ⟨⟨i, hi, hix⟩, hxn⟩ := hxU
    -- We have x / 9 = 10^k + r / 9.
    -- To show that x / 9 ∈ U(n) we need to show that x / 9 = 9^j for some j < 4001
    -- and Nat.log 10 (x / 9) = Nat.log 10 x = n.
    have eq : x / 9 = 10 ^ k + r / 9 := by rw [hx, hd, Nat.mul_add_div (by norm_num)]
    constructor
    -- Show that x / 9 = 9 ^ (i - 1).
    · use i - 1
      refine ⟨by omega, ?_⟩
      rw [← hix]
      -- It is enough to show that i ≠ 0.
      by_cases hi : i = 0
      -- If i = 0 then 1 = 9^0 = x = 9 * 10^k + r is impossible.
      · subst i d x
        omega
      nth_rw 3 [show 9 = 9 ^ 1 by norm_num]
      rw [Nat.pow_div (by omega) (by norm_num)]
    -- Show that Nat.log 10 (x / 9) = n.
    · apply Nat.log_eq_of_pow_le_of_lt_pow
      -- Show that 10 ^ n ≤ Nat.log 10 (x / 9) = Nat.log 10 (10^k + r / 9) with k = n.
      · rw [eq, hk, hxn]
        omega
      -- Show that x / 9 < 10 ^ (n + 1) = 10^(k + 1)
      · rw [eq, hk, hxn]
        suffices r < 10 ^ n by omega
        rwa [← hxn, ← hk]
  -- Prove that #U(n) = 2 implies that U(n) has exactly one element with the first digit
  -- equal to 9.
  have hU2 {n} (h : (U n).card = 2) : ((U n).filter p).card = 1 := by
    -- #U(n) = 2 implies that U(n) = {x, y} for some x and y.
    rw [card_eq_two] at h
    have ⟨x, y, hxy, hu⟩ := h
    -- Without loss of generality, assume that x < y.
    wlog h : x < y generalizing x y
    · apply this y x hxy.symm _ (by omega)
      simp [hu, pair_comm]
    -- We have U(n) ⊆ {z, 9 * z} for some z.
    have ⟨z, hz⟩ := hU n
    -- From #U(n) = 2 and x < y it follows that x = z and y = 9 * z.
    have ⟨hx, hy⟩ : x = z ∧ y = 9 * z := by
      have hx : x ∈ ({z, 9 * z} : Finset ℕ) := by
        apply mem_of_subset hz
        simp [hu]
      have hy : y ∈ ({z, 9 * z} : Finset ℕ) := by
        apply mem_of_subset hz
        simp [hu]
      simp only [mem_insert, mem_singleton] at hx hy
      omega
    subst x y
    -- We can write 9 * z = d * 10^k + r with 0 < d < 10 and r < 10^k, k Nat.log 10 (9 * z).
    have ⟨k, d, r, hk, hz, hd1, hd2, hr⟩ := hfirst (show 9 * z ≠ 0 by omega)
    -- Consider two cases: d = 9 and d < 9.
    cases' show d = 9 ∨ d < 9 by omega with hd hd
    · subst d
      simp [hu]
      -- If d = 9, show that the first digit of 9 * z is 9 and the first digit of z is not 9.
      suffices ¬ p z ∧ p (9 * z) by simp [filter_insert, this, filter_singleton]
      dsimp [p]
      constructor
      -- We have z = 1 * 10^k + r / 9 with r / 9 < 10^k so the first digit of z is 1.
      · have eq : z = 1 * 10 ^ k + r / 9 := by omega
        rw [hlast eq (by norm_num) (by norm_num) (by omega)]
        norm_num
      -- We have 9 * z = 9 * 10^k + r with r < 10^k so the first digit of z is 9.
      · rw [hlast hz (by norm_num) (by norm_num) hr]
    · suffices z ∉ U n by simp [hu] at this
      -- Now assume that d < 9 and derive a contradiction by showing that z ∉ U(n).
      simp [U]
      intro _
      -- It is enough to show that Nat.log 10 z < n.
      apply ne_of_lt
      apply Nat.log_lt_of_lt_pow (by omega)
      -- We have n = k.
      have hnk : n = k := by
        have : 9 * z ∈ U n := by simp [hu]
        simp [U] at this
        rw [hk, this.2]
      rw [hnk]
      -- Show that 9 * z < 9 * 10 ^ k.
      apply Nat.lt_of_mul_lt_mul_left (a := 9)
      -- 9 * z = d * 10^k + r < 8 * 10^k + 10^k.
      rw [hz, show 9 * 10 ^ k = 8 * 10 ^ k + 10 ^ k by ring]
      apply add_lt_add_of_le_of_lt _ hr
      apply Nat.mul_le_mul_right _ (by omega)
  -- Prove that #U(n) ≤ 2.
  have hU3 n : (U n).card ≤ 2 := by
    -- The result follows from U(n) ⊆ {x, 9 * x} for some x.
    have ⟨x, hx⟩ := hU n
    apply le_trans (card_le_card hx) card_le_two
  -- Prove an auxiliary lemma:
  -- Nat.log 10 (9 * x) ≤ Nat.log 10 x + 1.
  have hlog9 {x} (hx : x ≠ 0) : Nat.log 10 (9 * x) ≤ Nat.log 10 x + 1 := calc
    Nat.log 10 (9 * x) ≤ Nat.log 10 (x * 10) := Nat.log_mono_right (by omega)
    _ = Nat.log 10 x + 1 := Nat.log_mul_base (by norm_num) (by omega)
  -- Prove another auxiliary lemma:
  -- Nat.log 10 (9^(n + 1)) = Nat.log 10 (9^n) + 1 or
  -- Nat.log 10 (9^(n + 1)) = Nat.log 10 (9^n) and Nat.log 10 (9^(n + 2)) = Nat.log 10 (9^n) + 1.
  have hlog9' n : Nat.log 10 (9 ^ (n + 1)) = Nat.log 10 (9 ^ n) + 1 ∨ Nat.log 10 (9 ^ (n + 1)) = Nat.log 10 (9 ^ n) ∧ Nat.log 10 (9 ^ (n + 2)) = Nat.log 10 (9 ^ n) + 1 := by
    by_cases h : Nat.log 10 (9 ^ (n + 1)) = Nat.log 10 (9 ^ n)
    · right
      simp only [h, true_and]
      apply eq_of_le_of_le
      · rw [← h, show 9 ^ (n + 2) = 9 * 9 ^ (n + 1) by ring]
        apply hlog9 (by positivity)
      · rw [← Nat.log_mul_base (by norm_num) (by positivity)]
        apply Nat.log_mono_right
        rw [pow_add]
        omega
    · left
      rw [pow_succ, mul_comm] at h ⊢
      have := @hlog9 (9 ^ n) (by positivity)
      suffices Nat.log 10 (9 ^ n) ≤ Nat.log 10 (9 * 9 ^ n) by omega
      apply Nat.log_mono_right
      omega
  -- Prove that U(n) contains at least one element for each n ∈ I.
  have hU4 {n} (hn : n ∈ I) : 1 ≤ (U n).card := by
    simp only [mem_range, I] at hn
    suffices 0 < #(U n) by omega
    rw [card_pos, Nonempty.eq_1]
    -- It is enough to show that there exists i < 4001 such that Nat.log 10 (9^i) = n.
    simp [U, S]
    -- Proof by induction on n.
    induction n with
    -- If n = 0 then Nat.log 10 (9^0) = 0.
    | zero => use 0; norm_num
    | succ n ih =>
      -- Consider n + 1 < 3817 and find j < 4001 such that Nat.log 10 (9^j) = n + 1.
      -- From the induction hypothesis we get i < 4001 such that Nat.log 10 (9^i) = n.
      have ⟨i, hi, hin⟩ := ih (by omega)
      -- Show that i ≠ 4000.
      have hi0 : i ≠ 4000 := by
        -- If i = 4000 then Nat.log 10 (9^i) = Nat.log 10 (9^4000) = 3816.
        -- 3816 ≠ n because n < 3816.
        contrapose! hin
        rw [hin]
        omega
      -- Consider two cases: Nat.log 10 (9^(i + 1)) = n + 1
      -- and Nat.log 10 (9^(i + 1)) = n, Nat.log 10 (9^(i + 2)) = n + 1.
      rcases hlog9' i with hi1 | ⟨hi1, hi2⟩
      · use i + 1
        rw [hi1, hin]
        omega
      · use i + 2
        rw [hi2, hin]
        suffices i + 1 ≠ 4000 by omega
        contrapose! hi1
        rw [hin, hi1]
        omega
  -- Now we are ready to prove the main result.
  -- We need to find the size of S.filter p.
  rw [show {x ∈ T | (Nat.digits 10 x).getLastI = 9} = S.filter p by simp [hTS]]
  rw [Set.ncard_coe_Finset]
  -- Define I2 = elements n of I such that #U(n) = 2.
  set I2 := I.filter (fun n => (U n).card = 2)
  -- Prove that 4001 = #(I \ I2) + 2 * #I2.
  have eq1 : 4001 = (I \ I2).card + 2 * I2.card := calc
    -- We have 4001 = #S
    --              = #(⋃ n ∈ I, U(n))
    --              = ∑ n ∈ I, #U(n) (because sets U(n) are pairwise disjoint)
    --              = ∑ n ∈ (I \ I2), #(U n) + ∑ n ∈ I2, #(U n)
    --              = ∑ n ∈ (I \ I2), 1 + ∑ n ∈ I2, 2
    -- (because #U(n) = 2 for n ∈ I2 and #U(n) = 1 for n ∉ I2 since 1 ≤ #U(n) ≤ 2 for n ∈ I).
    4001 = #S := by simp only [card_map, card_range, S]
    _ = #(I.biUnion U) := by rw [hSU]
    _ = ∑ n ∈ I, #(U n) := by rw [card_biUnion hU_disj]
    _ = ∑ n ∈ (I \ I2), #(U n) + ∑ n ∈ I2, #(U n) := by simp only [filter_subset, sum_sdiff, I2]
    _ = ∑ n ∈ (I \ I2), 1 + ∑ n ∈ I2, 2 := by
        apply congr_arg₂ <;> apply sum_congr rfl
        · simp only [mem_sdiff, mem_filter, not_and, and_imp, I2]
          intro n hn h
          specialize hU3 n
          specialize hU4 hn
          specialize h hn
          omega
        · simp only [mem_filter, and_imp, imp_self, implies_true, I2]
    _ = #(I \ I2) + 2 * #I2 := by simp only [sum_const, smul_eq_mul, mul_comm, one_mul]
  -- Prove that #(S.filter p) = #I2.
  have eq2 : (S.filter p).card = I2.card := calc
    -- We have #(S.filter p) = #(⋃ n ∈ I, U(n).filter p)
    --       = ∑ n ∈ (I \ I2), #((U n).filter p) + ∑ n ∈ I2, #((U n).filter p)
    --       = ∑ n ∈ (I \ I2), 0 + ∑ n ∈ I2, 1
    -- (because #(U(n).filter p) = 0 for n ∈ I \ I2 and #(U(n).filter p) = 1 for n ∈ I2.).
    #(S.filter p) = #(I.biUnion (fun n => (U n).filter p)) := by simp only [hSU, filter_biUnion]
    _ = ∑ n ∈ I, #((U n).filter p) := by
        rw [card_biUnion]
        intro i hi j hj hij
        apply disjoint_filter_filter
        exact hU_disj hi hj hij
    _ = ∑ n ∈ (I \ I2), #((U n).filter p) + ∑ n ∈ I2, #((U n).filter p) := by simp only [filter_subset, sum_sdiff, I2]
    _ = ∑ n ∈ (I \ I2), 0 + ∑ n ∈ I2, 1 := by
        apply congr_arg₂ <;> apply sum_congr rfl
        · simp only [mem_sdiff, mem_filter, not_and, and_imp, I2]
          intro i hi h
          specialize hU3 i
          specialize h hi
          exact hU1 (by omega)
        · simp only [mem_filter, and_imp, I2]
          intro i hi hu
          exact hU2 hu
    _ = #I2 := by simp only [sum_const_zero, sum_const, smul_eq_mul, mul_one, zero_add]
  -- Rewrite eq1 as 4001 = #I - #I2 + 2 * #I2.
  rw [card_sdiff (by simp [I2])] at eq1
  -- We have #I = 3817 and #I2 ≤ #I so
  -- 4001 = #I - #I2 + 2 * #I2 implies #I2 = 4001 - #I = 4001 - 3817 = 184.
  suffices #I = 3817 ∧ #I2 ≤ #I by omega
  -- The result follows from #(S.filter p) = #I2 = 184.
  simp [I2, card_filter_le]
  simp [I]