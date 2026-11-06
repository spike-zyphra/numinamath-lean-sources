import Mathlib

/-
  Determine all positive integers $n$ for which $\frac{n^{2}+1}{[\sqrt{n}]^{2}+2}$ is an integer. Here $[r]$ denotes the greatest integer less than or equal to $r$.
-/
theorem number_theory_261170 (n : ℤ) (hn : n > 0) :
  (∃ N : ℤ, N = (n ^ 2 + 1 : ℝ) / (⌊ Real.sqrt n ⌋ ^ 2 + 2)) ↔ False := by

  -- we need the following lemmas
  -- lemma 1 : if x ^ 2 - y ^ 2 = 1, then it must be y = 0
  have lem_1 (x y : ℤ) (h : x ^ 2 - y ^ 2 = 1) : y = 0 := by
    suffices h : |y| = 0 by exact abs_eq_zero.mp h
    nth_rw 1 [← sq_abs] at h
    nth_rw 2 [← sq_abs] at h
    have : |x| ^ 2 > |y| ^ 2 := by linarith
    have : |x| > |y| := by
      apply (pow_lt_pow_iff_left₀ (abs_nonneg y) (abs_nonneg x) (show 2 ≠ 0 by norm_num)).mp
      exact this
    by_contra! h'
    have : |y| > 0 := by
      apply lt_of_le_of_ne
      exact abs_nonneg y
      exact h'.symm
    have : |x| - |y| ≥ 1 := by linarith
    have : |x| + |y| ≥ 2 := by linarith
    rw [sq_sub_sq] at h
    have : (|x| + |y|) * (|x| - |y|) ≥ 2 := by
      rw [show (2 : ℤ) = 2 * 1 by norm_num]
      apply mul_le_mul
      repeat assumption
      norm_num
      linarith
    linarith

  -- lemma 2 : (x ^ 2) % 8 is one of 0, 1, 4
  have lem2 (x : ℤ) : (x ^ 2) % 8 = 0 ∨ (x ^ 2) % 8 = 1 ∨ (x ^ 2) % 8 = 4 := by
    have : (x ^ 2) % 8 = (((x % 8) ^ 2) % 8) := by
      rw [pow_two, pow_two]
      exact Int.mul_emod x x 8
    rw [this]
    have : x % 8 < 8 := Int.emod_lt_of_pos x (by norm_num)
    have : x % 8 ≥ 0 := Int.emod_nonneg x (by norm_num)
    interval_cases x % 8
    all_goals simp

  -- lemma 3 : (x ^ 2) % 3 is one of 0, 1
  have lem3 (x : ℤ) : (x ^ 2) % 3 = 0 ∨ (x ^ 2) % 3 = 1 := by
    have : (x ^ 2) % 3 = (((x % 3) ^ 2) % 3) := by
      rw [pow_two, pow_two]
      exact Int.mul_emod x x 3
    rw [this]
    have : x % 3 < 3 := Int.emod_lt_of_pos x (by norm_num)
    have : x % 3 ≥ 0 := Int.emod_nonneg x (by norm_num)
    interval_cases x % 3
    all_goals simp

  -- We will show that there are no positive integers $n$ satisfying the condition of the problem.
  constructor
  ·
    rintro ⟨N, hN⟩

    field_simp at hN
    norm_cast at hN

    -- Let $m=[\sqrt{n}]$ and $a=n-m^{2}$.
    let m : ℤ := ⌊ Real.sqrt n ⌋
    let a := n - m ^ 2

    -- it follows that n ^ 2 + 1 is divisible by m ^ 2 + 2
    have h_dvd_0 : m ^ 2 + 2 ∣ n ^ 2 + 1 := by exact Dvd.intro_left N hN

    -- we can write (n ^ 2 + 1) = (m ^ 2 + a) ^ 2 + 1
    have : (n ^ 2 + 1) = (m ^ 2 + a) ^ 2 + 1 := by unfold a; ring
    rw [this] at h_dvd_0

    -- expanding (m ^ 2 + a) ^ 2 + 1 = (m ^ 2 + 2) * (m ^ 2 + 2 * a - 2) + ((a - 2) ^ 2 + 1)
    have : (m ^ 2 + a) ^ 2 + 1 = (m ^ 2 + 2) * (m ^ 2 + 2 * a - 2) + ((a - 2) ^ 2 + 1) := by ring
    rw [this] at h_dvd_0

    -- we deduce that m ^ 2 + 2 ∣ (a - 2) ^ 2 + 1
    have : m ^ 2 + 2 ∣ (m ^ 2 + 2) * (m ^ 2 + 2 * a - 2) := by apply Int.dvd_mul_right
    have h_dvd : m ^ 2 + 2 ∣ ((a - 2) ^ 2 + 1) := by exact (Int.dvd_iff_dvd_of_dvd_add h_dvd_0).mp this

    -- so let k be such that (a - 2) ^ 2 + 1 = k * (m ^ 2 + 2)
    obtain ⟨k, hk⟩ := h_dvd
    have k_ge_1 : k ≥ 1 := by nlinarith

    -- note that m > (√ n) - 1
    have m_gt : m > Real.sqrt n - 1 := Int.sub_one_lt_floor √↑n

    -- we have m ≥ 1 since n ≥ 1.
    have m_pos : m > 0 := by
      suffices h : (m : ℝ) > 0 by norm_cast at h
      suffices h : Real.sqrt n ≥ 1 by linarith
      simp; norm_cast

    -- also, n < (m + 1) ^ 2 as m + 1 > √ n
    have n_lt : n < (m + 1) ^ 2 := by
      suffices h : (n : ℝ) < (m + 1) ^ 2 by norm_cast at h
      have : (Real.sqrt n) ^ 2 = n := by apply Real.sq_sqrt; norm_cast; exact Int.le_of_lt hn
      rw [← this]
      apply pow_lt_pow_left₀
      linarith
      exact Real.sqrt_nonneg ↑n
      norm_num

    -- also, n ≤ m ^ 2 as m ≤ √ n
    have m_le : m ≤ Real.sqrt n := Int.floor_le √↑n
    have n_ge : n ≥ m ^ 2 := by
      suffices h : (n : ℝ) ≥ m ^ 2 by norm_cast at h
      have : (Real.sqrt n) ^ 2 = n := by apply Real.sq_sqrt; norm_cast; exact Int.le_of_lt hn
      rw [← this]
      apply pow_le_pow_left₀
      · norm_cast; exact Int.le_of_lt m_pos
      exact m_le

    -- so we deduce two bounds for a - 2 = n - m ^ 2 - 2
    have : a - 2 ≥ -2 := by unfold a; linarith
    have : a - 2 ≤ 2 * m - 2 := by unfold a; rw [add_pow_two] at n_lt; linarith

    -- using these bounds, we show (a - 2) ^ 2 + 1 ≤ max 4 ((2 * m - 2) ^ 2) + 1
    have : (a - 2) ^ 2 + 1 ≤ max 4 ((2 * m - 2) ^ 2) + 1 := by
      simp
      by_cases h : a - 2 ≥ 0
      ·
        right
        exact pow_le_pow_left₀ h this 2
      left
      have : a - 2 ≤ 0 := by linarith
      rw [show (4 : ℤ) = 2 ^ 2 by ring]
      apply sq_le_sq'
      all_goals linarith

    -- by routine calculation, max 4 ((2 * m - 2) ^ 2) + 1 < (m ^ 2 + 2) * 4
    have : max 4 ((2 * m - 2) ^ 2) + 1 < (m ^ 2 + 2) * 4 := by
      suffices h : max 4 ((2 * m - 2) ^ 2) < (m ^ 2 + 2) * 4 - 1 by linarith
      apply max_lt_iff.mpr
      constructor
      · calc
          (m ^ 2 + 2) * 4 - 1 = 4 * m ^ 2 + 7 := by ring
          _ ≥ 7 := by simp; exact sq_nonneg m
          _ > 4 := by norm_num
      · calc
          (2 * m - 2) ^ 2 = 4 * (m ^ 2 + 2) - 1 - (8 * m + 3) := by ring
          _ < 4 * (m ^ 2 + 2) - 1 := by simp; linarith
          _ = (m ^ 2 + 2) * 4 - 1 := by ring

    -- so we deduce k < 4 from the above two inequalities
    have : k < 4 := by
      have h1 : (m ^ 2 + 2) * k < (m ^ 2 + 2) * 4 := by linarith
      have h2 : (m ^ 2 + 2) ≥ 0 := by linarith [sq_nonneg m]
      apply Int.lt_of_mul_lt_mul_left h1 h2

    -- there are 3 cases
    interval_cases k
    · -- Case 1. When $k=1$. We get $(a-2)^{2}-m^{2}=1$, and this implies that
      -- $a-2= \pm 1, m=0$ must hold, but this contradicts with fact $m \geq 1$.
      have : (a - 2) ^ 2 - m ^ 2 = 1 := by linarith
      have : m = 0 := by exact lem_1 (a - 2) m this
      linarith
    · -- Case 2. When $k=2$. We have $(a-2)^{2}+1=2\left(m^{2}+2\right)$ in this case,
      -- but any perfect square is congruent to $0,1,4 \bmod 8$, and therefore, we have
      -- $(a-2)^{2}+1 \equiv 1,2,5(\bmod 8)$, while $2\left(m^{2}+2\right) \equiv 4,6(\bmod 8)$.
      -- Thus, this case cannot occur either.
      have hk' : ((a - 2) ^ 2 + 1) % 8 = (m ^ 2 + 2) * 2 % 8 := by congr
      rw [Int.add_emod, add_mul] at hk'
      nth_rw 2 [Int.add_emod] at hk'
      nth_rw 1 [Int.mul_emod] at hk'

      rcases lem2 (a - 2) with h | h | h
      repeat {
        rcases lem2 m with h' | h' | h'
        repeat {
            rw [h, h'] at hk'
            simp at hk'
        }
      }
    · -- Case 3. When $k=3$. We have $(a-2)^{2}+1=3\left(m^{2}+2\right)$ in this case.
      -- Since any perfect square is congruent to 0 or $1 \bmod 3$, we have $(a-2)^{2}+1 \equiv 1,2(\bmod 3)$,
      -- while $3\left(m^{2}+2\right) \equiv 0$ $(\bmod 3)$, which shows that this case cannot occur either.
      have hk' : ((a - 2) ^ 2 + 1) % 3 = (m ^ 2 + 2) * 3 % 3 := by congr
      have : (m ^ 2 + 2) * 3 % 3 = 0 := by simp
      rw [this] at hk'
      rw [Int.add_emod] at hk'

      rcases lem3 (a - 2) with h | h
      all_goals {rw [h] at hk'; simp at hk'}

  · simp
