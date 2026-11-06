import Mathlib

open Finset

/-Let $B$ be an integer such that its units digit is 7 (i.e., $B \equiv 7 \pmod{10}$). Let $K$ be a positive integer. Juan writes the list of pairs $(n, B^n)$, for $n=1, 2, 3, \dots$ on a chalkboard. As he writes the list, he underlines the pairs $(n, B^n)$ for which $n$ and $B^n$ have the same units digit.
Let $(N, B^N)$ be the $K^{th}$ underlined pair.
Show that $N = 10(K-1)+3$ if $K$ is odd, and $N = 10(K-1)+7$ if $K$ is even.-/
theorem number_theory_637163 (B K : ℕ) (hB : B ≡ 7 [MOD 10]) (Kpos : 0 < K):
    Nat.nth (fun n => n ≡ B ^ n [MOD 10]) K = if Even K then 10 * K + 3 else 10 * K + 7 := by
  simp [Nat.ModEq] at *
-- Prove that powers of $B$ modulo $10$ have a cycle of length $4$
  have pow_cycle : ∀ t, B ^ (4 * t) % 10 = 1 ∧ B ^ (4 * t + 1) % 10 = 7 ∧
  B ^ (4 * t + 2) % 10 = 9 ∧ B ^ (4 * t + 3) % 10 = 3 := by
    intro t; induction t with
    | zero =>
      simp; nth_rw 2 [Nat.pow_mod]
      rw [Nat.pow_mod, hB]; simp
    | succ t ih =>
      have ih1 : B ^ (4 * (t + 1)) % 10 = 1 := by
        rw [show 4 * (t + 1) = 4 * t + 3 + 1 by ring]
        rw [pow_succ, Nat.mul_mod, hB]; omega
      have ih2 : B ^ (4 * (t + 1) + 1) % 10 = 7 := by
        rw [pow_succ, Nat.mul_mod, hB]; omega
      have ih3 : B ^ (4 * (t + 1) + 2) % 10 = 9 := by
        rw [pow_succ, Nat.mul_mod, hB]; omega
      have ih4 : B ^ (4 * (t + 1) + 3) % 10 = 3 := by
        rw [pow_succ, Nat.mul_mod, hB]; omega
      split_ands; all_goals assumption
-- Prove that the condition in question is equivalent to $n % 20 = 3$ or $n % 20 = 17$
  have aux : (fun n => n % 10 = B ^ n % 10) = fun n => n % 20 = 3 ∨ n % 20 = 17 := by
    ext n; constructor
    · intro hn; rw [← Nat.div_add_mod n 4] at hn
      have := Nat.mod_lt n (show 4>0 by simp)
      specialize pow_cycle (n / 4)
      interval_cases mod4 : n % 4
      simp at hn; all_goals omega
    intro h; specialize pow_cycle (n / 4)
    rcases h with h|h
    · nth_rw 2 [← Nat.div_add_mod n 4]
      rw [show n % 10 = 3 by omega, show n % 4 = 3 by omega]
      omega
    nth_rw 2 [← Nat.div_add_mod n 4]
    rw [show n % 10 = 7 by omega, show n % 4 = 1 by omega]
    omega
-- Rewrite the goal by `aux` and `Nat.count`
  simp [aux, Nat.even_iff]
  suffices : Nat.count (fun n => n % 20 = 3 ∨ n % 20 = 17) (if K % 2 = 0 then 10 * K + 3 else 10 * K + 7) = K
  · nth_rw 1 [← this, Nat.nth_count]
    split_ifs with Kpar; all_goals omega
-- Apply `Nat.count_eq_card_filter_range` and the goal becomes counting cardinalities
  rw [Nat.count_eq_card_filter_range]
  rw [filter_or, card_union_of_disjoint]
  have : ∀ x ∈ range (if K % 2 = 0 then 10 * K + 3 else 10 * K + 7), x % 20 = 3 ↔
  x ≡ 3 [MOD 20] := by simp [Nat.ModEq]
  rw [filter_congr this, ← @Nat.cast_inj ℤ]
  push_cast; replace this : ∀ x ∈ range (if K % 2 = 0 then 10 * K + 3 else 10 * K + 7), x % 20 = 17 ↔
  x ≡ 17 [MOD 20] := by simp [Nat.ModEq]
  rw [filter_congr this, range_eq_Ico]
-- Split the goal depending on the parity of $K$
  split_ifs with Kpar
  -- When $K$ is even, apply `Nat.Ico_filter_modEq_card` to compute cardinality
  · repeat rw [Nat.Ico_filter_modEq_card, max_eq_left]
    simp; nth_rw 1 [show (20:ℚ) = 10*2 by ring, mul_div_mul_left]
  -- Simplify `Int.ceil`, the goal follows
    norm_num [Int.ceil_eq_zero_iff.mpr]
    rw [show (10:ℚ)*K+3-17 = 10*K-14 by ring, sub_div]
    nth_rw 1 [show (20:ℚ) = 10*2 by ring, mul_div_mul_left]
    rw [show (2:ℚ) = (2:ℕ) by rfl, ← Nat.cast_div]
    rw [Int.ceil_natCast, sub_eq_add_neg]; nth_rw 2 [add_comm]
    rw [Int.ceil_add_nat]
    norm_num [Int.ceil_eq_zero_iff]
    norm_cast; any_goals omega
    any_goals positivity
    · rw [← sub_nonneg]
      norm_num [Int.ceil_eq_zero_iff.mpr]
      apply Int.ceil_nonneg; apply div_nonneg
      rw [sub_nonneg]; norm_cast
      omega; simp
    rw [← sub_nonneg]
    norm_num [Int.ceil_eq_zero_iff.mpr]
    apply Int.ceil_nonneg; positivity
-- When $K$ is odd, apply `Nat.Ico_filter_modEq_card` to compute cardinality
  repeat rw [Nat.Ico_filter_modEq_card, max_eq_left]
  simp; nth_rw 1 2 [show K = 2*(K / 2) + 1 by omega]
  push_cast; ring_nf
-- Simplify `Int.ceil`, the goal follows
  rw [Int.ceil_add_nat, Int.ceil_natCast]
  replace this : ⌈(7 : ℚ) / 10⌉ = 1 := by
    norm_num [Int.ceil_eq_iff]
  rw [this]; norm_cast; omega
  · norm_num [Int.ceil_eq_zero_iff.mpr]
    rw [show K = 2*(K / 2) + 1 by omega]
    push_cast; ring_nf; positivity
  any_goals simp
  norm_num [Int.ceil_eq_zero_iff.mpr]
  rw [show K = 2*(K / 2) + 1 by omega]
  push_cast; ring_nf; positivity
  rw [disjoint_filter]; omega