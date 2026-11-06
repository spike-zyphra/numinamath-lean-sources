import Mathlib

/-The sequences of positive integers $1,a_2, a_3, \dots$ and $1,b_2, b_3, \dots$ are an increasing arithmetic sequence and an increasing geometric sequence, respectively. Let $c_n=a_n+b_n$. There is an integer $k$ such that $c_{k-1}=100$ and $c_{k+1}=1000$. Find $c_k$.-/
theorem algebra_16451 (a b c : ℕ → ℤ) (ha : ∃ d, ∀ n, a n = 1 + d * n)
  (hb : ∃ r, ∀ n, b n = r ^ n) (hc : ∀ n, c n = a n + b n)
  (amono : ∀ m n, m < n → a m < a n) (bmono : ∀ m n, m < n → b m < b n)
  (h : c k = 100 ∧ c (k + 2) = 1000) : c (k + 1) = 262 := by
    -- Let $d$ be the common difference, and let $r$ be the common ratio,
    -- so $d$ and $r$ are positive integers.
    obtain ⟨d, hd⟩ := ha
    obtain ⟨r, hr⟩ := hb
    rw [hc k, hc (k + 2), hd k, hr k, hd (k + 2), hr (k + 2)] at h
    -- so
    -- \begin{align*}
    -- 1 + (k - 2) d + r^{k - 2} &= 100, \\
    -- 1 + kd + r^k &= 1000.
    -- \end{align*}Then
    -- \begin{align*}
    -- (k - 2) d + r^{k - 2} &= 99, \\
    -- kd + r^k &= 999.
    -- \end{align*}
    have ⟨c1, c2⟩ : d * k + r^k = 99 ∧ d * (k + 2) + r^(k + 2) = 999 := by
      split_ands <;> norm_cast <;> linarith
    have : k ≠ 0 := fun k0 => by simp [k0] at c1
    -- Since the geometric sequence is increasing, $r > 1$
    have rge1 : 1 < r := by
      have := bmono 0 1 (by omega)
      simp [hr 0, hr 1] at this
      tauto
    -- Since the arithmetic sequence is increasing, $d > 0$
    have dpos : 0 < d := by
      have := amono 0 1
      simp [hd 0, hd 1] at this
      tauto
    by_cases k1 : 1 < k
    · -- From the second equation, $r^k < 999.$  If $k \ge 4,$ then $r < 999^{1/4},$
      have : r^4 < 999 := calc
        _ ≤ r^(k + 2) := (pow_le_pow_iff_right rge1).2 (by omega)
        _ < _ := by nlinarith
      -- so $r \le 5.$
      have rle5 : r ≤ 5 := by
        by_contra!
        have : 999 < r^4 := calc
          _ < (6 : ℤ)^4 := by norm_num
          _ ≤ _ := pow_le_pow_left (by simp) this 4
        linarith
      interval_cases r
      · -- If $r = 2,$ then the only possible values of $k$ are 4, 5, 6, 7, and 8.
        -- We find that none of these values work.
        have : k ≤ 6 := by
          have : 2^k < 2^7 := by nlinarith
          have : k < 7 := (pow_lt_pow_iff_right (by omega)).1 this
          linarith
        interval_cases k <;> simp at c1 c2 <;> linarith
      · -- If $r = 3,$ then the only possible values of $k$ are 4, 5, and 6.
        -- We find that none of these values work.
        have : k ≤ 4 := by
          have : 3^k < 3^5 := by nlinarith
          have : k < 5 := (pow_lt_pow_iff_right (by omega)).1 this
          linarith
        interval_cases k <;> simp at c1 c2 <;> linarith
      · -- If $r = 4,$ then the only possible values of $k$ is 4.
        -- We find that this value does not work.
        have : k < 5 := by
          have : 4^ k < 4 ^ 5 := by nlinarith
          exact (pow_lt_pow_iff_right (by omega)).1 this
        interval_cases k <;> simp at c1 c2 <;> linarith
      · -- If $r = 5,$ then the only possible values of $k$ is 4.
        -- We find that this value does not work.
        have : k < 3 := by
          have : 5^k < 5^3 := by nlinarith
          exact (pow_lt_pow_iff_right (by omega)).1 this
        interval_cases k; simp at c1 c2; linarith
      -- Therefore, we must have $k = 1,$ so
      -- \begin{align*}
      -- d + r &= 99, \\
      -- 3d + r^3 &= 999.
      -- \end{align*}
    · have : k = 1 := by omega
      simp [this] at c1 c2 ⊢
      -- From the first equation, $d = 99 - r.$  Substituting, we get
      -- \[3(99 - r) + r^3 = 999,\]so $r^3 - 3r - 702 = 0.$
      have cd : d = 99 - r := by linarith
      rw [cd] at c2
      -- This factors as $(r - 9)(r^2 + 9r + 78) = 0,$ so $r = 9,$ so $d = 90.$
      -- Then $a_3 = 1 + 2 \cdot 90 = 181$ and $c_3 = 9^2 = 81,$ and $c_3 = 181 + 81 = \boxed{262}.$
      have : (r - 9) * (r^2 + 9 * r + 78) = 0 := by linarith
      have r9 : r = 9 := by
        rw [mul_eq_zero] at this
        have tmp : r ^ 2 + 9 * r + 78 ≠ 0 := by nlinarith
        simp [tmp] at this
        omega
      simp [r9] at cd
      simp [hc 2, hd 2, hr 2, r9, cd]
