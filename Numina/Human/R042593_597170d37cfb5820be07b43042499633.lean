import Mathlib

/- The base-`b` expansion of `n`. -/
def baseExpansion {b} (hb : b > 1) : ℕ → List ℕ
| 0 => []
| n + 1 => (n + 1) % b :: baseExpansion hb ((n + 1) / b)
decreasing_by
  simp only [Nat.succ_eq_add_one, invImage]
  sorry

/- The list length of `baseExpansion` in certain range of `n`. -/
lemma length_baseExpansion_range {b n} (hb : b > 1) (k : ℕ) (hn : b ^ k ≤ n ∧ n < b ^ (k + 1)) :
    (baseExpansion hb n).length = k + 1 := by
  induction k generalizing n with
  | zero =>
   simp only [pow_zero, zero_add, pow_one] at hn
   obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := by sorry
   simp only [hm, baseExpansion, List.length_cons, zero_add, add_left_eq_self, List.length_eq_zero]
   simp [← hm, baseExpansion, Nat.div_eq_of_lt hn.2]
  | succ m hm =>
   obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := by
      -- simp only [Nat.exists_eq_add_one]
      -- calc
      --    _ < b ^ (m + 1) := by apply Nat.pos_pow_of_pos; linarith
      --    _ ≤ _ := hn.1
      sorry
   simp only [hk, baseExpansion, List.length_cons, add_left_inj]
   apply hm
   rw [Nat.div_lt_iff_lt_mul (by linarith), Nat.le_div_iff_mul_le (by linarith)]
   simpa [← Nat.pow_add_one, ← hk]

/- Show that the base \( b \) expansion of a positive integer \( n \) has \( \left[\log_{b} n\right] + 1 \) digits. -/
theorem number_theory_4467 {b n} (hb : b > 1) (hn : n > 0) :
    (baseExpansion hb n).length = ⌊Real.logb b n⌋₊ + 1 := by
  set k := ⌊Real.logb b n⌋₊
  apply length_baseExpansion_range
  rify at hb hn ⊢
  simp only [← Real.rpow_natCast]
  -- logarithm identity : n = b^logb n
  have n_eq : (n : ℝ) = b ^ (Real.logb b n) := by
    symm
    apply Real.rpow_logb
    repeat linarith
  -- k = ⌊logb n⌋
  replace k_eq : (k : ℝ) = (⌊Real.logb b n⌋ : ℤ) := by
    simp only [k]
    apply natCast_floor_eq_intCast_floor
    apply Real.logb_nonneg
    assumption
    norm_cast at hn ⊢
  nth_rw 1 2 [n_eq]
  constructor
  -- n ≤ bk
  · rw [Real.rpow_le_rpow_left_iff (by assumption), k_eq]
    apply Int.floor_le
  -- bk < n+1
  · rw [Real.rpow_lt_rpow_left_iff (by assumption)]
    push_cast
    rw [k_eq]
    apply Int.lt_floor_add_one
