import Mathlib

open Real Finset

/- 3. Find all natural values of $n$ for which
$$
\cos \frac{2 \pi}{9}+\cos \frac{4 \pi}{9}+\cdots+\cos \frac{2 \pi n}{9}=\cos \frac{\pi}{9}, \text { and } \log _{2}^{2} n+45<\log _{2} 8 n^{13}
$$
In your answer, write the sum of the obtained values of $n$.

(6 points) -/
theorem algebra_229558 :
    ∑ᶠ n ∈ {n : ℕ | ∑ k ∈ Icc 1 n, cos (2 * π * k / 9) = cos (π / 9) ∧ logb 2 n ^ 2 + 45 < logb 2 (8 * n ^ 13)}, n = 644 := by
  set s := {n : ℕ | _}
  -- It is enough to show that the set from the theorem statement is equal to
  -- (fun x => 2 + 9 * x) '' [7, 13].
  suffices s = (Icc 7 13).map ⟨(2 + 9 * ·), by simp [Function.Injective]⟩ by
    rw [this, finsum_mem_eq_toFinset_sum]
    simp [sum_Icc_succ_top]
  ext n
  simp [s]
  -- Prove that all solutions of
  -- ∑ k ∈ [1, n], cos (2 * π * k / 9) = cos (π / 9) are
  -- n = 2 + 9 * m for some m ∈ ℕ.
  have eq1 : ∑ k ∈ Icc 1 n, cos (2 * π * k / 9) = cos (π / 9) ↔ ∃ m, n = 2 + 9 * m := calc
    -- Multiply both sides of the equality by 2 * sin (π / 9) ≠ 0.
    _ ↔ 2 * sin (π / 9) * ∑ k ∈ Icc 1 n, cos (2 * π * k / 9) = 2 * sin (π / 9) * cos (π / 9) := by
      rw [mul_right_inj']
      apply ne_of_gt
      apply mul_pos zero_lt_two
      apply sin_pos_of_pos_of_lt_pi <;> linarith [pi_pos]
    -- Show that 2 * sin (π / 9) * ∑ k ∈ [1, n], cos (2 * π * k / 9)
    --     = sin ((π / 9) * (2 * n + 1)) - sin (π / 9).
    _ ↔ sin ((π / 9) * (2 * n + 1)) - sin (π / 9) = sin (2 * (π / 9)) := by
      rw [sin_two_mul]
      suffices 2 * sin (π / 9) * ∑ k ∈ Icc 1 n, cos (2 * π * k / 9) = sin ((π / 9) * (2 * n + 1)) - sin (π / 9) by
        rw [this]
      calc
        _ = ∑ k ∈ Icc 1 n, 2 * sin (π / 9) * cos (2 * π * k / 9) := by
          rw [mul_sum]
        -- We have 2 * sin (π / 9) * cos (2 * π * k / 9)
        --      = sin (π / 9 - 2 * π * k / 9) + sin (π / 9 + 2 * π * k / 9)
        --      = sin (π / 9 * (2 * (k + 1) - 1)) - sin (π / 9 * (2 * k - 1)).
        _ = ∑ k ∈ Icc 1 n, (sin (π / 9 * (2 * (k + 1) - 1)) - sin (π / 9 * (2 * k - 1))) := by
          apply sum_congr rfl
          intro k hk
          rw [two_mul_sin_mul_cos, ← neg_sub, sin_neg]
          ring_nf
        -- ∑ k ∈ [1, n], f(k) = ∑ k ∈ [0, n), f (k + 1).
        _ = ∑ k ∈ range n, (sin (π / 9 * (2 * (k + 1 : ℕ) + 1)) - sin (π / 9 * (2 * k + 1))) := by
          rw [show Icc 1 n = Ico 1 (n + 1) from rfl, sum_Ico_eq_sum_range]
          apply sum_congr rfl
          intro k hk
          push_cast
          ring_nf
        -- ∑ k ∈ [0, n), (f (k + 1) - f k) = f n - f 0.
        -- We have f k = sin (π / 9 * (2 * k + 1)) so we get
        -- sin (π / 9 * (2 * n + 1)) - sin (π / 9).
        _ = sin ((π / 9) * (2 * n + 1)) - sin (π / 9) := by
          rw [sum_range_sub (fun k : ℕ => sin (π / 9 * (2 * k + 1)))]
          simp only [CharP.cast_eq_zero, mul_zero, zero_add, mul_one]
    -- Show that sin (2 * π / 9)  + sin (π / 9) = sin (4 * π / 9).
    _ ↔ sin ((π / 9) * (2 * n + 1)) = sin (4 * π / 9) := by
      rw [sub_eq_iff_eq_add]
      suffices sin (2 * (π / 9)) + sin (π / 9) = sin (4 * π / 9) by rw [this]
      calc
        _ = 2 * sin (π / 6) * cos (π / 18) := by
          rw [two_mul_sin_mul_cos]
          ring_nf
        _ = sin (4 * π / 9) := by
          rw [sin_pi_div_six, show π / 18 = π / 2 - 4 * π / 9 by ring]
          rw [cos_pi_div_two_sub]
          ring
    -- sin ((π / 9) * (2 * n + 1)) - sin (4 * π / 9) = 2 * sin (π * n / 9 - π / 6) * cos (π * n / 9 + 5 * π / 18).
    _ ↔ 2 * sin (π * n / 9 - π / 6) * cos (π * n / 9 + 5 * π / 18) = 0 := by
      rw [two_mul_sin_mul_cos, ← sub_eq_zero]
      ring_nf
      rw [neg_div, mul_neg, sin_neg]
      rfl
    -- Write down all solutions of the equations sin x = 0 and cos y = 0 with
    -- x = π * n / 9 - π / 6 and y = π * n / 9 + 5 * π / 18.
    _ ↔ (∃ k : ℤ, k * π = π * n / 9 - π / 6) ∨ (∃ k : ℤ, π * n / 9 + 5 * π / 18 = (2 * k + 1) * π / 2) := by
      simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      rw [sin_eq_zero_iff, cos_eq_zero_iff]
    -- Multiply solutions by 18 / π and get
    -- 2 * n = 18 * k + 3 for k ∈ ℤ or n = 2 + 9 * k for k ∈ ℤ.
    _ ↔ (∃ k : ℤ, 18 * k + 3 = 2 * n) ∨ (∃ k : ℤ, n = 2 + 9 * k) := by
      have eq1 (k : ℤ) : k * π = π * n / 9 - π / 6 ↔ 18 * k + 3 = 2 * n := by
        rify
        symm
        rw [← mul_right_inj' (show π / 18 ≠ 0 by linarith [pi_pos])]
        constructor <;> intro h <;> linear_combination h
      have eq2 (k : ℤ) : π * n / 9 + 5 * π / 18 = (2 * k + 1) * π / 2 ↔ n = 2 + 9 * k := by
        rify
        symm
        rw [← mul_right_inj' (show π / 9 ≠ 0 by linarith [pi_pos])]
        constructor <;> intro h <;> linear_combination h
      simp [eq1, eq2]
    -- 2 * n = 18 * k + 3 is impossible because 2 * n is even and 18 * k + 3 is odd.
    -- n = 2 + 9 * k for k ∈ ℤ is equivalent to n = 2 + 9 * k for k ∈ ℕ because n ≥ 0.
    _ ↔ ∃ m, n = 2 + 9 * m := by
      constructor
      · intro h
        rcases h with ⟨k, hk⟩ | ⟨k, hk⟩
        · omega
        · use k.toNat
          omega
      · intro ⟨m, hm⟩
        right
        use m
        norm_cast
  -- Assume that n > 0 and show that the solutions of the inequality
  -- logb 2 n ^ 2 + 45 < logb 2 (8 * n ^ 13) are n ∈ (2^6, 2^7).
  have eq2 (n : ℕ) (hn : 0 < n) : logb 2 n ^ 2 + 45 < logb 2 (8 * n ^ 13) ↔ n ∈ Ioo (2 ^ 6) (2 ^ 7) := calc
    _ ↔ logb 2 n ^ 2 + 45 < 3 + 13 * logb 2 n := by
      rw [logb_mul (by norm_num) (by positivity), logb_pow]
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, logb_pow, logb_self_eq_one one_lt_two]
      ring_nf
    -- Rewrite the inequality as
    -- (logb 2 n - 6) * (logb 2 n - 7) < 0.
    _ ↔ (logb 2 n - 6) * (logb 2 n - 7) < 0 := by
      rw [← sub_neg]
      ring_nf
    -- We get 6 < logb 2 n < 7.
    _ ↔ 6 < logb 2 n ∧ logb 2 n < 7 := by
      rw [mul_neg_iff]
      constructor <;> intro h
      · cases' h with h h
        · constructor <;> linarith
        · linarith
      · left
        constructor <;> linarith
    -- We conclude that 2^6 < n < 2^7.
    _ ↔ n ∈ Ioo (2 ^ 6) (2 ^ 7) := by
      simp only [Nat.reducePow, mem_Ioo]
      rify at hn ⊢
      rw [logb_lt_iff_lt_rpow one_lt_two hn, lt_logb_iff_rpow_lt one_lt_two hn]
      norm_num
  rw [eq1]
  constructor
  -- It is easy to show that the intersection of solutions of the equality and
  -- the inequality from the theorem statement is equal to
  -- n = 2 + 9 * m for m ∈ [7, 13].
  · intro ⟨⟨m, hm⟩, h⟩
    rw [eq2 n (by omega)] at h
    use m
    simp only [Nat.reducePow, mem_Ioo] at h
    omega
  · intro ⟨m, hm, hmn⟩
    rw [eq2 n (by omega)]
    simp only [Nat.reducePow, mem_Ioo]
    refine ⟨⟨m, hmn.symm⟩, ?_⟩
    omega