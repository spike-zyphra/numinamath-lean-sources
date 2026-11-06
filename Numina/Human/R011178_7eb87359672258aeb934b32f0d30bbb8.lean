import Mathlib

/--
Let's call the distance between numbers the absolute value of their difference. It is known that the sum of the distances from sixteen consecutive natural numbers to some number
a is 276, and the sum of the distances from these same sixteen numbers to some number b is 748.
Find all possible values of a, given that a+b=62.5.
-/

--this lemma shows that for any point x ∈ [0,15], ∑|x-k-i| ≤ 120 
lemma distance_in_icc (x : ℝ) (k : ℕ) (h : k ≤ x ∧ x ≤ k + 15) :
  Finset.sum (Finset.Icc (0 : ℕ) 15) (fun i => abs (x - (k + i))) ≤ 120 := by
    rw[(by ring_nf : (120 : ℝ) = (8 : ℕ) • 15), (by simp : 8 = (Finset.Icc (0 : ℕ) 7).card), ← Finset.sum_const (15 : ℝ)]
    have sum_eq_sum_reindex : Finset.sum (Finset.Icc (0 : ℕ) 15) (fun i => abs (x - (k + i))) =
        Finset.sum (Finset.Icc (0 : ℕ) 7) (fun i => abs (x - (k + i)) + abs (x - (k + (15 - i)))) := by
      rw[Finset.sum_add_distrib, ← Nat.Ico_succ_right 0 7]
      rw[Nat.succ_eq_add_one, (by norm_num : 7 + 1 = 8)]
      have fun_eq_fun : ∀ i ∈ Finset.Ico (0 : ℕ) 8 , |x - (k + (15 - i))| = |x - (k + ((15 - i) : ℕ))| := by
        intro i hi
        simp at hi
        rw[Nat.cast_sub (by linarith)]
        rfl
      rw[Finset.sum_congr rfl fun_eq_fun]
      rw[@Finset.sum_Ico_reflect _ _ (fun j => |x - (k + j)|) 0 8 15 (by linarith)]
      rw[← Nat.Ico_succ_right 0 15]
      simp
      rw[(by norm_num : 8 = 0 + 8), (by norm_num : 16 = 8 + 8), ← Finset.sum_Ico_add]
      simp
      have fun_eq_fun' : ∀ i ∈ Finset.range 8 , |x - (k + (8 + i))| = |x - (k + ((8 + i) : ℕ))| := by
        intro i hi
        simp at hi
        norm_cast
      rw[Finset.sum_congr rfl fun_eq_fun']
      rw[← Finset.sum_range_add (fun j => |x - (k + j)|) 8 8]
    rw[sum_eq_sum_reindex]
    have : ∀ i ∈ Finset.Icc (0 : ℕ) 7, |x - (k + i)| + |x - (k + (15 - i))| ≤ 15 := by
      intro i hi
      simp at hi
      let s := (k : ℝ) + i
      let t := k + ((15 : ℝ) - i)
      have s_le_t : s ≤ t := by 
        simp[s,t]
        rw[le_sub_iff_add_le, ← mul_two]
        norm_cast
        linarith
      by_cases hxs : x ≤ s
      · have hxt : x ≤ t := by rify at s_le_t; linarith
        simp[s,t] at hxs hxt
        push_cast at hxt
        rw[abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
      · by_cases hsxt : s < x ∧ x < t
        · simp[s,t] at hsxt
          push_cast at hsxt
          rw[abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          linarith
        · have htx : t ≤ x := by push_neg at hxs hsxt; specialize hsxt hxs; exact hsxt
          have hsx : s ≤ x := by rify at s_le_t; linarith
          simp[s,t] at hsx htx
          push_cast at htx
          rw[abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
    exact Finset.sum_le_sum this

theorem algebra_155146 {k : ℕ} {a b : ℝ}
    (hdist_a : Finset.sum (Finset.Icc (0 : ℕ) 15) (fun i => abs (a - (k + i))) = 276)
    (hdist_b : Finset.sum (Finset.Icc (0 : ℕ) 15) (fun i => abs (b - (k + i))) = 748)
    (hab : a + b = 125 / 2) : a = - 3 / 4 := by
  --a and b cannot be into [k, k+15] because any x ∈ [k, k+15] has sum of distances equal to 120 by the lemma above
  have a_nin_icc : a < k ∨ a > k + 15 := by
    by_contra h
    push_neg at h
    have := distance_in_icc a k h
    linarith
  have b_nin_icc : b < k ∨ b > k + 15 := by
    by_contra h
    push_neg at h
    have := distance_in_icc b k h
    linarith
  -- Σ|-|=|Σ-| in the a case, because ∀ i ∈ [0,15], either a < k + i or a > k + i, hence the absolute value resolves in the same way and the sign can be collected outside of the big sum
  have a_sum_abs_eq_abs_sum : Finset.sum (Finset.Icc (0 : ℕ) 15) (fun i => abs (a - (k + i))) =
      abs (Finset.sum (Finset.Icc (0 : ℕ) 15) fun i => a - (k + i)) := by
        symm
        rw[abs_eq (Finset.sum_nonneg (by intro i hi; exact abs_nonneg (a - (k + i))))]
        obtain ha1|ha2 := a_nin_icc
        · have fun_eq_fun : ∀ i ∈ Finset.Icc (0 : ℕ) 15, |a - (k + i)| = -(a - (k + i)) := by
            intro i hi
            simp at hi
            have : a - (k + i) ≤ 0 := by linarith
            rw[abs_of_nonpos this]
          rw[Finset.sum_congr rfl fun_eq_fun]
          right
          simp
        · have fun_eq_fun : ∀ i ∈ Finset.Icc (0 : ℕ) 15, |a - (k + i)| = a - (k + i) := by
            intro i hi
            simp at hi
            have : a - (k + i) > 0 := by rify at hi; linarith
            rw[abs_of_nonneg (le_of_lt this)]
          rw[Finset.sum_congr rfl fun_eq_fun]
          left
          simp
  -- Σ|-|=|Σ-| in the b case, because ∀ i ∈ [0,15], either b < k + i or b > k + i, hence the absolute value resolves in the same way and the sign can be collected outside of the big sum
  have b_sum_abs_eq_abs_sum : Finset.sum (Finset.Icc (0 : ℕ) 15) (fun i => abs (b - (k + i))) =
      abs (Finset.sum (Finset.Icc (0 : ℕ) 15) fun i => b - (k + i)) := by
        symm
        rw[abs_eq (Finset.sum_nonneg (by intro i hi; exact abs_nonneg (b - (k + i))))]
        obtain ha1|ha2 := b_nin_icc
        · have fun_eq_fun : ∀ i ∈ Finset.Icc (0 : ℕ) 15, |b - (k + i)| = -(b - (k + i)) := by
            intro i hi
            simp at hi
            have : b - (k + i) ≤ 0 := by linarith
            rw[abs_of_nonpos this]
          rw[Finset.sum_congr rfl fun_eq_fun]
          right
          simp
        · have fun_eq_fun : ∀ i ∈ Finset.Icc (0 : ℕ) 15, |b - (k + i)| = b - (k + i) := by
            intro i hi
            simp at hi
            have : b - (k + i) > 0 := by rify at hi; linarith
            rw[abs_of_nonneg (le_of_lt this)]
          rw[Finset.sum_congr rfl fun_eq_fun]
          left
          simp
  rw[a_sum_abs_eq_abs_sum] at hdist_a
  rw[b_sum_abs_eq_abs_sum] at hdist_b
  --one is able to split the bug sum into bug sums by distributivity of the big sum over add and sub
  rw[Finset.sum_sub_distrib, Finset.sum_add_distrib] at hdist_a hdist_b
  --big sum of a constant is constant times the cardinality of the set you sum over
  rw[Finset.sum_const a, Finset.sum_const (k : ℝ)] at hdist_a
  rw[Finset.sum_const b, Finset.sum_const (k : ℝ)] at hdist_b
  rw[← Nat.Ico_succ_right 0 15] at hdist_a hdist_b
  norm_num at hdist_a hdist_b
  rw[(by norm_num : (120 : ℝ) = 16 * (15 / 2))] at hdist_a hdist_b
  rw[← mul_add, ← mul_sub, abs_mul] at hdist_a hdist_b
  simp at hdist_a hdist_b
  obtain ha1|ha2 := a_nin_icc
  --one has a system of three equations in a b k with an absolute value.
  --There are 4 cases to distinguish but all of them are solved by linear arithmetic
  · have a_summand_neg : a - ((k : ℝ) + 15 / 2) < 0 := by linarith
    obtain hb1|hb2 := b_nin_icc
    --case a < k and b < k
    · have b_summand_neg : b - ((k : ℝ) + 15 / 2) < 0 := by linarith
      rw[abs_of_neg (a_summand_neg)] at hdist_a
      rw[abs_of_neg (b_summand_neg)] at hdist_b
      have hdist_a' := CancelDenoms.cancel_factors_eq_div hdist_a (by linarith)
      have hdist_b' := CancelDenoms.cancel_factors_eq_div hdist_b (by linarith)
      have ha : a = ((k : ℝ) + 15 / 2) - 276 / 16 := by linarith
      have hb : b = ((k : ℝ) + 15 / 2) - 748 / 16 := by linarith
      rw[ha, hb] at hab
      --k = 223/4 cannot be since k is in ℕ
      have hk : (k : ℝ) = 223 / 4 := by linarith
      push_cast at hk
      field_simp at hk
      norm_cast at hk
      have := Dvd.intro_left k hk
      contradiction
    --case a < k and b > k + 15
    · have b_summand_pos : b - ((k : ℝ) + 15 / 2) > 0 := by linarith
      rw[abs_of_neg (a_summand_neg)] at hdist_a
      rw[abs_of_pos (b_summand_pos)] at hdist_b
      have hdist_a' := CancelDenoms.cancel_factors_eq_div hdist_a (by linarith)
      have hdist_b' := CancelDenoms.cancel_factors_eq_div hdist_b (by linarith)
      have ha : a = ((k : ℝ) + 15 / 2) - 276 / 16 := by linarith
      have hb : b = ((k : ℝ) + 15 / 2) + 748 / 16 := by linarith
      rw[ha, hb] at hab
      --k = 9 then substitute back in the equation in k and a to obtain the claim
      have hk : (k : ℝ) = 9 := by linarith
      rw[hk] at hdist_a
      ring_nf at hdist_a
      linarith
  · have a_summand_pos : a - ((k : ℝ) + 15 / 2) > 0 := by linarith
    obtain hb1|hb2 := b_nin_icc
    --case a > k + 15 and b < k
    · have b_summand_neg : b - ((k : ℝ) + 15 / 2) < 0 := by linarith
      rw[abs_of_pos (a_summand_pos)] at hdist_a
      rw[abs_of_neg (b_summand_neg)] at hdist_b
      have hdist_a' := CancelDenoms.cancel_factors_eq_div hdist_a (by linarith)
      have hdist_b' := CancelDenoms.cancel_factors_eq_div hdist_b (by linarith)
      have ha : a = ((k : ℝ) + 15 / 2) + 276 / 16 := by linarith
      have hb : b = ((k : ℝ) + 15 / 2) - 748 / 16 := by linarith
      rw[ha, hb] at hab
      --k = 77/2 cannot be since k is in ℕ
      have hk : (k : ℝ) = 77 / 2 := by linarith
      push_cast at hk
      field_simp at hk
      norm_cast at hk
      have := Dvd.intro_left k hk
      contradiction
    --case a > k + 15 and b > k + 15
    · have b_summand_pos : b - ((k : ℝ) + 15 / 2) > 0 := by linarith
      rw[abs_of_pos (a_summand_pos)] at hdist_a
      rw[abs_of_pos (b_summand_pos)] at hdist_b
      have hdist_a' := CancelDenoms.cancel_factors_eq_div hdist_a (by linarith)
      have hdist_b' := CancelDenoms.cancel_factors_eq_div hdist_b (by linarith)
      have ha : a = ((k : ℝ) + 15 / 2) + 276 / 16 := by linarith
      have hb : b = ((k : ℝ) + 15 / 2) + 748 / 16 := by linarith
      rw[ha, hb] at hab
      --k is negative, but it cannot be since k is in ℕ
      have hk : 0 = 1 := by linarith
      contradiction