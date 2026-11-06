import Mathlib

open Finset

/- A sequence of positive integers $a_{1}, a_{2}, \ldots, a_{2017}$ has the property that for all integers $m$ where $1 \leq m \leq 2017,3\left(\sum_{i=1}^{m} a_{i}\right)^{2}=\sum_{i=1}^{m} a_{i}^{3}$. Compute $a_{1337}$. -/
theorem algebra_609747
  (a: ℕ → ℤ)
  (hpos: ∀ n: ℕ, 1 ≤ n → n ≤ 2017 → a n > 0)
  (h: ∀ m: ℕ, 1 ≤ m → m ≤ 2017 → 3 * (∑ i ∈ Icc 1 m, a i) ^ 2 = ∑ i ∈ Icc 1 m, a i ^ 3) :
  a 1337 = 4011 := by

  -- prove a m = 3 * m and 2 * ∑ i ∈ Icc 1 m, a i = 3 * m * (m+1) in one induction
  have h1: ∀ m : ℕ , 1 ≤ m → m ≤ 2017 → a m = 3 * m ∧ 2 * ∑ i ∈ Icc 1 m , a i = 3 * m * (m+1) := by
    intro m hm1 hm2

    -- induction actually from m=1
    induction m with
    | zero => linarith
    | succ d hd =>
      by_cases hd1: d = 0
      . -- if d = 0, while m = 1
        simp [hd1]
        -- we can get a 1 = 3 from h, and ∑ i ∈ Icc 1 m, a i = 3 * m * (m+1) by linarith
        have : a 1 = 3 := by
          have h1_1 := h 1 (by linarith) (by linarith)
          simp [Finset.Icc_self, Finset.sum_singleton] at h1_1
          simp [sq, pow_three] at h1_1
          cases h1_1
          . linarith
          . have : a 1 > 0 := hpos 1 (by linarith) (by linarith)
            linarith
        constructor ; all_goals linarith

      -- if d ≠ 0, then d >= 1
      have hd1: d > 0 := by positivity
      have hd1: d >= 1 := by linarith
      -- and assume for 1..d, h1 is right
      have hd := hd (by linarith) (by linarith)

      -- then we start from h (d+1)
      have h1_1: 3 * (∑ i ∈ Icc 1 (d+1), a i) ^ 2 = ∑ i ∈ Icc 1 (d+1), a i ^ 3 := by
        apply h (d+1); all_goals linarith

      -- slice the sum for d+1 into sum for d and a (d+1), now 3 * (∑ k ∈ Icc 1 d, a k + a (d + 1)) ^ 2 = ∑ k ∈ Icc 1 d, a k ^ 3 + a (d + 1) ^ 3
      rw [sum_Icc_succ_top, sum_Icc_succ_top] at h1_1; all_goals try linarith

      -- simp h1_1 into  3 * (3 * d * (d + 1) * a (d + 1)) + 3 * a (d + 1) ^ 2 = a (d + 1) ^ 3
      rw [add_sq, mul_add, mul_add, h d hd1 (by linarith), add_assoc, add_left_cancel_iff, hd.2] at h1_1
      rw [sq, pow_three] at h1_1 ; simp [← mul_assoc] at h1_1 ; rw [← add_mul] at h1_1
      have : a (d+1) > 0 := hpos (d+1) (by linarith) (by linarith)

      -- rewrite into  9 * ↑d * (↑d + 1) + 3 * a (d + 1) = a (d + 1) * a (d + 1)
      rw [mul_right_cancel_iff_of_pos this] at h1_1

      -- rewrite into (a (d+1) - (3*d+3)) * (a (d+1) + 3*d) = 0
      have h1_2: (a (d+1) - (3*d+3)) * (a (d+1) + 3*d) = 0 := by
        rw [sub_mul, mul_add, mul_add]
        simp [← h1_1]
        linarith

      -- then we can get a (d + 1) = 3 * d + 3 or a (d + 1) = 0
      simp at h1_2
      cases h1_2 with
      | -- so we can get a (d + 1) = 3 * (d + 1) and
        inl h1_2 =>
        have h1_3: a (d+1) = 3 * d + 3 := by
          rw [sub_eq_zero] at h1_2
          rw [h1_2]
        constructor
        . exact h1_3

        -- and 2 * ∑ i ∈ Icc 1 (d + 1), a i = 3 * (d + 1) * ((d + 1) + 1)
        rw [sum_Icc_succ_top, mul_add, hd.2] ; all_goals try linarith
        simp [h1_3]
        norm_num [add_mul, mul_add]
        linarith
      | -- a (d + 1) = 0 has contradiction with hpos
        inr h1_2 => linarith

  -- we only need the first part of h1 to get final answer
  have h2: ∀ m : ℕ , 1 ≤ m → m ≤ 2017 → a m = 3 * m := by
    intro m hm1 hm2
    exact h1 m hm1 hm2 |>.left

  -- calc final answer
  calc a 1337 = a (1336 + 1) := by rfl
    _ = 3 * 1336 + 3 := by
      apply h2 ; all_goals linarith
    _ = 4011 := by norm_num
