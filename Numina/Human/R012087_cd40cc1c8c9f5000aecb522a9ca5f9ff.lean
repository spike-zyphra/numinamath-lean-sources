import Mathlib

open Real Set Finset
open scoped BigOperators

-- The function x + 1 / x is increasing when 1 ≤ x
lemma add_one_div_self_inc_of_one_le {x y : ℝ}
    (hxy : x ≤ y) (h : 1 ≤ x) :
    x + 1 / x ≤ y + 1 / y := by
  -- Multiply both sides by x * y
  rw [← mul_le_mul_left (show 0 < x * y by nlinarith)]
  simp only [mul_add] --
  nth_rw 2 [mul_comm x y, mul_assoc]
  rw [mul_assoc x y (1 / y)]
  rw [mul_one_div_cancel (show x ≠ 0 by positivity), mul_one_div_cancel (show y ≠ 0 by linarith), mul_one, mul_one]
  -- Move terms to LHS
  rw [← sub_nonneg]
  -- Factor the LHS
  suffices 0 ≤ (x * y - 1) * (y - x) by
    calc
      0 ≤ _ := this
      _ = _ := by linarith
  -- Simple actoring
  apply mul_nonneg
  · nlinarith
  linarith

-- The function x + 1 / x is at least 2
lemma two_le_add_one_div_self_of_pos {x : ℝ}
    (h : 0 < x) :
    2 ≤ x + 1 / x := by
  -- Multiply by x
  rw [← mul_le_mul_left (by linarith)]
  simp [mul_add, (show x ≠ 0 by linarith), ← pow_two]
  rw [← sub_nonneg]
  -- Use trivial inequality
  suffices 0 ≤ (x - 1) ^ 2 by
    linarith
  apply sq_nonneg


/- (2) Let $A_{k}=\left\{x \left\lvert\, x=k t+\frac{1}{k t}\right., \frac{1}{k^{2}} \leqslant t \leqslant 1\right\}(k=2,3, \cdots, 2012)$, then the intersection of all $A_{k}$ is ( ).
(A) $\varnothing$
(B) $\{2\}$
(C) $\left[2, \frac{5}{2}\right]$
(D) $\left[2, \frac{2012^{2}+1}{2012}\right]$ -/
theorem algebra_196477 {A : ℕ → Set ℝ}
  (hA : ∀ k ∈ Finset.Icc 2 2012, A k = {x | ∃ t : ℝ, x = k * t + 1 / (k * t) ∧ 1 / (k ^ 2) ≤ t ∧ t ≤ 1}) :
  ⋂ k ∈ Finset.Icc 2 2012, A k = {x | 2 ≤ x ∧ x ≤ 5 / 2} := by
  -- Characterize all A k
  have key : ∀ k ∈ Finset.Icc 2 2012, A k = {x | (2 : ℝ) ≤ x ∧ x ≤ k + 1 / k} := by
    -- Set up environment
    intro k hk
    rw [hA k hk]
    -- Use extensionality to prove equality of sets
    ext x
    dsimp
    constructor
    · -- Prove that if such t exists, then x is in the interval
      rintro ⟨t, rfl, ht, ht'⟩
      -- Show t is positive
      have t_pos : 0 < t := by
        calc
          0 < 1 / (k : ℝ) ^ 2 := by rw [one_div_pos]; norm_cast; simp at hk; nlinarith
          _ ≤ t := ht
      constructor
      · -- Use the fact that x + 1 / x is at least 2
        apply two_le_add_one_div_self_of_pos
        -- Show that k * t is positive
        apply mul_pos
        · simp at hk
          norm_cast
          linarith
        exact t_pos
      -- Do casework on whether t is above or below 1 / k and apply increasing lemma
      have : t ≤ 1 / k ∨ 1 / k < t := le_or_lt _ _
      rcases this with t_le | lt_t
      · -- Case when t ≤ 1 / k
        -- Bound 1 / (k * t)
        have bound_one_div_mul : 1 ≤ 1 / (k * t) ∧ 1 / (k * t) ≤ k := by
          constructor
          · -- Show 1 ≤ 1 / (k * t)
            -- Multiply by t
            rw [← div_div, ← mul_le_mul_left t_pos]
            rw [mul_one, mul_div_cancel₀ _ (show t ≠ 0 by linarith)]
            exact t_le
          -- Show 1 / (k * t) ≤ k
          rw [← div_div, ← mul_le_mul_left t_pos, mul_div_cancel₀ _ (show t ≠ 0 by linarith)]
          rw [← div_le_div_iff_of_pos_right (show (0 : ℝ) < k by simp at hk; norm_cast; linarith), div_div, ← pow_two, mul_div_cancel_right₀ t (by norm_cast; simp at hk; linarith)]
          exact ht
        -- Manipulate conditions
        nth_rw 1 [← one_div_one_div (k * t), add_comm]
        exact add_one_div_self_inc_of_one_le bound_one_div_mul.2 bound_one_div_mul.1
      apply add_one_div_self_inc_of_one_le
      · nlinarith
      rw [div_lt_iff₀ (by simp at hk; norm_cast; linarith)] at lt_t
      linarith
    -- Prove that if x is in the interval, then such t exists
    simp at hk
    rintro ⟨hx, hx'⟩
    -- By solving the equation x = k * t + 1 / (k * t) for t, we get a quadratic, and either solution works
    use (x + √ (x ^ 2 - 4)) / (2 * k)
    -- Show that the root expression is less than x. This will be used later
    have rt_lt_x : √ (x ^ 2 - 4) < x := by
      rw [← sq_lt_sq₀ (by positivity) (by positivity), sq_sqrt (by nlinarith)]
      linarith
    constructor
    · -- Show that the solution actually works
      rw [← div_div, mul_div_cancel₀ _ (by norm_cast; linarith), ← div_mul]
      conv_rhs =>
        rhs
        -- Multiply by root conjugate to rationalize denominator
        rw [← mul_div_mul_right _ _ (show x - √ (x ^ 2 - 4) ≠ 0 by linarith), one_mul, ← sq_sub_sq, sq_sqrt (by nlinarith), ← sub_add, sub_self, zero_add]
        lhs; rhs
        rw [show (4 : ℝ) = 2 * 2 by norm_num]
      rw [← div_div, div_mul, div_self (by positivity), div_one]
      ring
    constructor
    · -- Show that solution satisfies the lower bound of 1 / k ^ 2
      rw [← mul_le_mul_right (show 0 < (k : ℝ) ^ 2 by norm_cast; nlinarith), div_mul_cancel₀ _ (by norm_cast; nlinarith), ← div_div, pow_two (k : ℝ), ← mul_assoc, div_mul_cancel₀ _ (by norm_cast; nlinarith)]
      calc
        1 ≤ x / 2 := by linarith
        _ ≤ (x + √ (x ^ 2 - 4)) / 2 * 1 := by linarith [sqrt_nonneg (x ^ 2 - 4)]
        _ ≤ (x + √ (x ^ 2 - 4)) / 2 * k := by gcongr; norm_cast; linarith
    -- Show that solution satisfies upper bound of 1
    rw [div_le_one (by norm_cast; linarith)]
    calc
      -- Use the fact that x ≤ k + 1 / k
      _ ≤ k + 1 / k + √ (x ^ 2 - 4) := by linarith
      -- Use the fact that x ≤ k + 1 / k
      _ ≤ k + 1 / k + √ ((k + 1 / k) ^ 2 - 4) := by gcongr
      -- Simplify the square root
      _ = k + 1 / k + √ (k ^ 2 + (1 / k) ^ 2 - 2) := by
        conv_lhs =>
          rhs
          congr
          rw [add_sq, mul_assoc, mul_div_cancel₀ _ (by norm_cast; linarith), mul_one]
          rw [add_assoc, add_comm 2 _, add_sub_assoc, add_sub_assoc]
          norm_num
          rw [← one_div, ← sub_eq_add_neg, ← add_sub_assoc, show (1 : ℝ) = 1 ^ 2 by simp, ← div_pow]
      -- Factor as a square
      _ = k + 1 / k + √ ((k - 1 / k) ^ 2) := by
        conv_rhs =>
          rhs
          congr
          rw [sub_sq, mul_assoc, mul_div_cancel₀ _ (by norm_cast; linarith), mul_one, sub_add_comm, add_comm, ← add_sub_assoc]
      -- Cancel the square and square root
      _ = k + 1 / k + (k - 1 / k) := by
        rw [sqrt_sq (by rw [sub_nonneg, ← mul_le_mul_right (show 0 < (k : ℝ) by norm_cast; linarith), div_mul_cancel₀ _ (by norm_cast; linarith)]; norm_cast; nlinarith)]
      _ = 2 * k := by ring
    -- Use extensionality
  ext x
  constructor
  · -- Prove that every element in the union lies in [2, 5 / 2]
    simp
    intro hx
    conv at hx =>
      ext i hi hi'
      -- Use key
      rw [key i (by simp; tauto)]
      dsimp
    rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num]
    exact ⟨by linarith [hx 2 (by norm_num) (by norm_num)], by linarith [hx 2 (by norm_num) (by norm_num)]⟩
  -- Prove that every element in [2, 5 / 2] lies in the union
  intro hx
  simp at hx
  simp
  intro k hk hk'
  -- Use the characterization of A k
  rw [key k (by simp; exact ⟨hk, hk'⟩)]
  dsimp
  refine ⟨hx.1, ?_⟩
  rify at hk
  -- Use increasing property of x + 1 / x
  calc
    x ≤ 5 / 2 := hx.2
    _ = 2 + 1 / 2 := by norm_num
    _ ≤ (k : ℝ) + 1 / k := add_one_div_self_inc_of_one_le hk (by linarith)