import Mathlib

/-4. $f(x)$ is a real-valued function defined on the set of real numbers $\mathbf{R}$ and satisfies: for any real numbers $x_{1}, x_{2}$, when $\left|x_{1}-x_{2}\right| \leqslant 1$ there is $\left|f\left(x_{2}\right)-f\left(x_{1}\right)\right| \leqslant 1$, and $f(0)=1$, prove: $-|x| \leqslant f(x)|\leqslant| x \mid+2$.-/
theorem inequalities_250953
  (f : ℝ → ℝ)
  (h₁ : ∀ x y, |x - y| ≤ 1 → |f x - f y| ≤ 1)
  (h₂ : f 0 = 1) :
  ∀ x, -|x| ≤ f x ∧ f x ≤ |x| + 2 := by

  -- 首先将条件推广至大于1的自然数：对所有x, y, 若 |x - y| ≤ n, 则 |f(x) - f(y)| ≤ n
  -- 使用归纳法即可
  have lem1 (n : ℕ) (npos : n ≥ 1) :
    ∀ x y : ℝ, |x - y| ≤ n → |f x - f y| ≤ n := by
      intro x y
      wlog hxy : x ≤ y
      · push_neg at hxy
        have := this f h₁ h₂ n npos y x (le_of_lt hxy)
        rw [abs_sub_comm]
        nth_rw 2 [abs_sub_comm]
        exact this

      induction n, npos using Nat.le_induction generalizing x y
      case base =>
        simp
        intro h_abs
        exact h₁ x y h_abs
      case succ n hn ih =>
        intro h_abs

        by_cases h_abs_le_n : |x - y| ≤ n
        · trans ↑n
          apply ih x y hxy h_abs_le_n
          norm_cast
          exact Nat.le_add_right n 1

        push_neg at h_abs_le_n
        rw [abs_sub_comm] at h_abs h_abs_le_n
        have : |y - x| = y - x := by
          apply abs_of_nonneg
          linarith only [hxy]
        rw [this] at h_abs h_abs_le_n

        let y' := y - 1
        have h_diff' : y' - x ≤ n := by
          rw [Nat.cast_add, Nat.cast_one] at h_abs
          unfold y'
          linarith only [h_abs]
        have h_pos' : y' - x ≥ 0 := by
          unfold y'
          suffices h : y - x ≥ 1 by linarith [h]
          trans ↑n
          exact le_of_lt h_abs_le_n
          norm_cast

        have : f x - f y = (f x - f y') + (f y' - f y) := by ring
        rw [this]

        trans |(f x - f y')| + |(f y' - f y)|
        · exact abs_add_le (f x - f y') (f y' - f y)

        rw [Nat.cast_add, Nat.cast_one]
        gcongr
        · apply ih
          linarith only [h_pos']
          rwa [abs_sub_comm, abs_of_nonneg]
          linarith only [h_pos']
        · apply h₁ y' y
          unfold y'
          simp only [sub_sub_cancel_left, abs_neg, abs_one, le_refl]

  -- 进一步，上述引理对n = 0也显然成立
  have lem2 (n : ℕ) :
    ∀ x y : ℝ, |x - y| ≤ n → |f x - f y| ≤ n := by
      intro x y h_abs
      by_cases hn : n = 0
      · rw [hn] at h_abs
        simp at h_abs
        have : x = y := by linarith only [h_abs]
        rw [this]
        simp

      have : n ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr hn
      exact lem1 n this x y h_abs

  intro x
  -- 为证明 -|x| ≤ f(x) ≤ |x| + 2， 只需证明 |f(x) - 1| ≤ |x| + 1
  suffices h : |f x - 1| ≤ |x| + 1 by
    apply abs_sub_le_iff.mp at h
    obtain ⟨ha, hb⟩ := h
    constructor <;> linarith

  -- 即只需证明 |f(x) - f(0)| ≤ |x| + 1
  nth_rw 1 [← h₂]
  by_cases hx : x > 0
  · -- 当 x > 0 时，令 k = ⌊x⌋
    let k := ⌊x⌋

    -- 则 |f x - f 0| = |f x - f k) + (f k - f 0)| ≤ |(f x - f k)| + |(f k - f 0)|
    have : f x - f 0 = (f x - f k) + (f k - f 0) := by ring
    rw [this]

    trans |(f x - f k)| + |(f k - f 0)|
    · exact abs_add_le (f x - f ↑k) (f ↑k - f 0)

    -- 由于 |x - k| ≤ 1，故 |f x - f ↑k| ≤ 1
    have : |f x - f ↑k| ≤ 1 := by
      apply h₁
      unfold k
      have : x - ⌊x⌋ ≥ 0 := by
        apply sub_nonneg.mpr
        exact Int.floor_le x
      rw [abs_of_nonneg this]
      have : x < ⌊x⌋ + 1 := by simp only [Int.lt_floor_add_one]
      linarith only [this]

    -- 根据lem2，有 |f k - f 0| ≤ |k| = k ≤ x = |x|
    have : |f ↑k - f 0| ≤ |x| := by
      trans ↑k
      swap
      · unfold k
        rw [abs_of_nonneg (le_of_lt hx)]
        exact Int.floor_le x
      · have : k = k.natAbs := by
          refine Int.eq_natAbs_of_zero_le ?_
          unfold k
          apply Int.floor_nonneg.mpr
          exact le_of_lt hx
        rw [this]
        have := lem2 k.natAbs k.natAbs 0 (by simp)
        norm_cast at this

    linarith

  by_cases hk : x = 0
  ·  -- 当 x = 0 时，显然成立
    rw [hk]
    simp only [sub_self, abs_zero, zero_add, zero_le_one]

  -- 当 x > 0 时，令 k = ⌈x⌉
  push_neg at hx hk
  have x_neg : x < 0 := by exact lt_of_le_of_ne hx hk

  let k := ⌈x⌉

  -- 则 |f x - f 0| = |f x - f k) + (f k - f 0)| ≤ |(f x - f k)| + |(f k - f 0)|
  have : f x - f 0 = (f x - f k) + (f k - f 0) := by ring
  rw [this]

  trans |(f x - f k)| + |(f k - f 0)|
  · exact abs_add_le (f x - f ↑k) (f ↑k - f 0)
  · -- 由于 |x - k| ≤ 1，故 |f x - f ↑k| ≤ 1
    have : |f x - f ↑k| ≤ 1 := by
      apply h₁
      unfold k
      have : x - ⌈x⌉ ≤ 0 := by
        apply sub_nonpos.mpr
        exact Int.le_ceil x
      rw [abs_of_nonpos this]
      simp only [neg_sub, tsub_le_iff_right, ge_iff_le]
      rw [add_comm]
      exact le_of_lt <| Int.ceil_lt_add_one x

    -- 根据lem2，有 |f k - f 0| ≤ |k| = -k ≤ -x = |x|
    have : |f ↑k - f 0| ≤ |x| := by
      trans -↑k
      swap
      · unfold k
        rw [abs_of_neg x_neg]
        simp
        exact Int.le_ceil x
      · have : k = -k.natAbs := by
          suffices h : -k = k.natAbs by exact Int.eq_neg_comm.mp h.symm
          refine Eq.symm (Int.ofNat_natAbs_of_nonpos ?_)
          unfold k
          refine Int.ceil_le.mpr ?_
          norm_cast
        rw [this]
        simp only [Int.cast_neg, neg_neg, ge_iff_le]
        have := lem2 k.natAbs (-k.natAbs) 0 (by simp)
        norm_cast at this
        simp at this
        simp
        trans ↑k.natAbs
        · exact this
        have : k.natAbs = (|k| : ℝ) := by
          norm_cast
          have : (k.natAbs : ℝ) = ↑(k.natAbs : ℤ) := by
            exact rfl
          rw [this]
          norm_cast
        rw [this]

    linarith
