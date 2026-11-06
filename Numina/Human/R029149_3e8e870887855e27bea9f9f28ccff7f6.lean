import Mathlib

open Real Finset

/- Let $f(n)$ be the integer closest to $\sqrt[4]{n}.$  Find $\sum_{k=1}^{1995}\frac 1{f(k)}.$ -/
theorem number_theory_53666 (f : ℕ → ℤ) (hf : ∀ n, f n = round ((n : ℝ) ^ ((1 : ℝ) / 4))) :
    ∑ k in Icc 1 1995, (1 / f k : ℝ) = 400 := by
  -- Prove that f is monotone.
  have hmono : Monotone f := by
    rw [show f = (fun n : ℕ => round ((n : ℝ) ^ (1 / 4 : ℝ))) by ext n; rw [hf]]
    -- round x = ⌊x + 1 / 2⌋
    simp_rw [round_eq]
    -- ⌊·⌋ is a monotone function so it is left to prove that n^(1/4) + 1/2 is monotone.
    apply Monotone.comp Int.floor_mono
    intro i j hij
    simp only [add_le_add_iff_right]
    -- i^(1/4) ≤ j^(1/4) iff i ≤ j.
    rwa [rpow_le_rpow_iff (by linarith) (by linarith) (by linarith), Nat.cast_le]
  -- f monotone and f(a) = f(b) implies that f(k) = f(a) for all k ∈ [a, b].
  have hconst {a b k : ℕ} (hab : f a = f b) (hk : k ∈ Finset.Icc a b) : f k = f a := by
    simp only [Finset.mem_Icc] at hk
    exact hmono.eq_of_le_of_le hab hk.1 hk.2
  -- Suppose that n ≥ 1 and (n - 1/2)^4 ≤ k < (n + 1/2)^4. Show that f k = n.
  have h (n : ℕ) (hn : n ≥ 1) {k : ℕ} : (n - 1 / 2 : ℝ) ^ 4 ≤ k ∧ k < (n + 1 / 2 : ℝ) ^ 4 → f k = n := by
    intro h
    have heq : ((k : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rify at hn
    -- round x = ⌊x + 1 / 2⌋ and ⌊x + 1 / 2⌋ = n iff n ≤ x + 1 / 2 < n + 1.
    rw [hf, round_eq, Int.floor_eq_iff, ← sub_le_iff_le_add]
    push_cast
    constructor
    -- Show that n ≤ k^(1/4) + 1/2 iff (n - 1/2)^4 ≤ k.
    · rw [← pow_le_pow_iff_left₀ (by linarith) (by positivity) (show 4 ≠ 0 by norm_num), heq]
      exact h.1
    -- Show that k^(1/4) + 1/2 < n + 1 iff k < (n + 1/2)^4.
    · have : ∀ x : ℝ, x + 1 / 2 < n + 1 ↔ x < n + 1 / 2 := by
        intro x
        constructor <;> (intro h; linarith)
      rw [this, ← pow_lt_pow_iff_left₀ (by positivity) (by linarith) (show 4 ≠ 0 by norm_num), heq]
      exact h.2
  -- Using the lemma proved above we can find values of f.
  -- We have f(1) = 1 and f(5) = 1, f(6) = 2 and f(39) = 2, etc.
  have f1 : f 1 = 1 ∧ f 5 = 1 := by constructor <;> (apply h 1 (by norm_num); norm_num)
  have f2 : f 6 = 2 ∧ f 39 = 2 := by constructor <;> (apply h 2 (by norm_num); norm_num)
  have f3 : f 40 = 3 ∧ f 150 = 3 := by constructor <;> (apply h 3 (by norm_num); norm_num)
  have f4 : f 151 = 4 ∧ f 410 = 4 := by constructor <;> (apply h 4 (by norm_num); norm_num)
  have f5 : f 411 = 5 ∧ f 915 = 5 := by constructor <;> (apply h 5 (by norm_num); norm_num)
  have f6 : f 916 = 6 ∧ f 1785 = 6 := by constructor <;> (apply h 6 (by norm_num); norm_num)
  have f7 : f 1786 = 7 ∧ f 1995 = 7 := by constructor <;> (apply h 7 (by norm_num); norm_num)
  -- Let g(k) = 1 / f(k).
  set g : ℕ → ℝ := fun k => 1 / f k
  -- Show that f(a) = f(b) and a ≤ b implies that ∑ k ∈ [a, b + 1), g(k) = (b - a + 1) / f(a).
  have hsum_const {a b : ℕ} (hab : a ≤ b) (hf : f a = f b) : ∑ k ∈ Ico a (b + 1), g k = (b - a + 1) / f a := calc
    -- g(k) is constant for k ∈ [a, b + 1) (because f(k) is constant).
    ∑ k ∈ Ico a (b + 1), g k = ∑ k ∈ Ico a (b + 1), g a := by
        apply sum_congr rfl
        intro k hk
        simp [g]
        exact hconst hf hk
    -- So the sum is equal to (b + 1 - a) * g(a) = (b - a + 1) / f(a).
    _ = (b - a + 1) / f a := by
        simp
        push_cast [show b + 1 ≥ a by omega]
        ring
  calc
    -- Compute the sum from the theorem statement.
    ∑ k ∈ Icc 1 1995, g k = ∑ k ∈ Ico 1 1996, g k := rfl
    -- Rewrite the sum as the sum of sums over intervals where f(k) is constant.
    _ = ∑ k ∈ Ico 1 6, g k + ∑ k ∈ Ico 6 40, g k + ∑ k ∈ Ico 40 151, g k + ∑ k ∈ Ico 151 411, g k
          + ∑ k ∈ Ico 411 916, g k + ∑ k ∈ Ico 916 1786, g k + ∑ k ∈ Ico 1786 1996, g k  := by
        repeat rw [sum_Ico_consecutive _ (by norm_num) (by norm_num)]
    -- Apply hsum_const to each sum and find sum values.
    _ = 5 / 1 + 34 / 2 + 111 / 3 + 260 / 4 + 505 / 5 + 870 / 6 + 210 / 7 := by
        repeat rw [hsum_const (by norm_num) (by linarith)]
        simp_rw [f1, f2, f3, f4, f5, f6, f7]
        norm_num
    -- Simplify the expression and get the final result.
    _ = 400 := by norm_num