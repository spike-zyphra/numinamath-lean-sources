import Mathlib

/- Determine all four digit numbers $\overline{a b c d}$ such that

$$
a(a+b+c+d)\left(a^{2}+b^{2}+c^{2}+d^{2}\right)\left(a^{6}+2 b^{6}+3 c^{6}+4 d^{6}\right)=\overline{a b c d}
$$ -/
theorem number_theory_605299 :
    {n | ∃ a b c d : ℕ, a ≠ 0 ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ a * (a + b + c + d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a ^ 6 + 2 * b ^ 6 + 3 * c ^ 6 + 4 * d ^ 6) = n ∧ n = 1000 * a + 100 * b + 10 * c + d} = {2010} := by
  -- Break the goal into two parts.
  ext n
  apply Iff.intro
  . intro h
    obtain ⟨a, b, c, d, ha', ha, hb, hc, hd, h₀, hn⟩ := h
    replace ha' : 1 ≤ a := by
      omega
    have ha'' : 1 ≤ a ^ 3 := by
      nlinarith only [show 1 ≤ a ^ 2 by nlinarith only [ha'], ha']
    replace ha'' : 1 ≤ a ^ 6 := by
      nlinarith only [ha'']
    -- First show that n ≥ (b + 1)(b² + 1)(2b⁶ + 1).
    have h₁ : n ≥ (b + 1) * (b ^ 2 + 1) * (2 * b ^ 6 + 1) := by
      calc
        n = a * (a + b + c + d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a ^ 6 + 2 * b ^ 6 + 3 * c ^ 6 + 4 * d ^ 6) := h₀.symm
        _ ≥ 1 * (1 + b) * (1 ^ 2 + b ^ 2) * (1 ^ 6 + 2 * b ^ 6) := by
          iterate 3 apply mul_le_mul
          . omega
          . omega
          . positivity
          . positivity
          . nlinarith only [ha']
          . positivity
          . positivity
          . linarith only [ha'', show 0 ≤ c ^ 6 by positivity, show 0 ≤ d ^ 6 by positivity]
          . positivity
          . positivity
        _ = (b + 1) * (b ^ 2 + 1) * (2 * b ^ 6 + 1) := by
          ring
    -- We get b ≤ 2.
    have h₂ : b ≤ 2 := by
      by_contra!
      -- Supose b ≥ 3, then n > 9999, contradiction.
      have habsurd : n > n := by
        calc
          n ≥ (b + 1) * (b ^ 2 + 1) * (2 * b ^ 6 + 1) := h₁
          _ ≥ (3 + 1) * (3 ^ 2 + 1) * (2 * 3 ^ 6 + 1) := by
            iterate 2 apply mul_le_mul
            . omega
            . nlinarith only [show 3 ≤ b by omega]
            . positivity
            . positivity
            . apply add_le_add
              . rw [mul_le_mul_left (by norm_num)]
                apply pow_le_pow (by omega) (by omega) (by rfl)
              . rfl
            . positivity
            . positivity
          _ > n := by
            omega
      absurd habsurd
      exact lt_irrefl n
    -- We further shows that b < 2.
    have h₃ : b < 2 := by
      by_contra!
      replace h₂ : b = 2 := by
        omega
      clear this
      -- Assume b = 2, then n ≥ 1935, hence a ≥ 2.
      have h₃ : a ≥ 2 := by
        by_contra!
        have habsurd : n > n := by
          calc
            n ≥ (b + 1) * (b ^ 2 + 1) * (2 * b ^ 6 + 1) := h₁
            _ ≥ (2 + 1) * (2 ^ 2 + 1) * (2 * 2 ^ 6 + 1) := by
              iterate 2 apply mul_le_mul
              . omega
              . nlinarith only [show 2 ≤ b by omega]
              . positivity
              . positivity
              . apply add_le_add
                . rw [mul_le_mul_left (by norm_num)]
                  apply pow_le_pow (by omega) (by omega) (by rfl)
                . rfl
              . positivity
              . positivity
            _ > n := by
              omega
        absurd habsurd
        exact lt_irrefl n
      -- Since a ≥ 2, we have b ≤ 1.
      have h₄ : b ≤ 1 := by
        by_contra!
        -- Suppose b ≥ 2, then n > 9999, contradiction.
        have habsurd : n > n := by
          calc
            n = a * (a + b + c + d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a ^ 6 + 2 * b ^ 6 + 3 * c ^ 6 + 4 * d ^ 6) := h₀.symm
            _ ≥ 2 * (2 + b) * (2 ^ 2 + b ^ 2) * (2 ^ 6 + 2 * b ^ 6) := by
              iterate 3 apply mul_le_mul
              . omega
              . omega
              . positivity
              . positivity
              . linarith only [show 2 ^ 2 ≤ a ^ 2 by nlinarith only [h₃], show 0 ≤ c ^ 2 by positivity, show 0 ≤ d ^ 2 by positivity]
              . positivity
              . positivity
              . linarith only [show 2 ^ 6 ≤ a ^ 6 by nlinarith only [show 2 ^ 2 ≤ a ^ 2 by nlinarith only [h₃], show 2 ^ 4 ≤ a ^ 4 by nlinarith only [show 2 ^ 2 ≤ a ^ 2 by nlinarith only [h₃]]], show 0 ≤ c ^ 6 by positivity, show 0 ≤ d ^ 6 by positivity]
              . positivity
              . positivity
            _ = 2 * (b + 2) * (b ^ 2 + 2 ^ 2) * (2 * b ^ 6 + 2 ^ 6) := by ring
            _ ≥ 2 * (2 + 2) * (2 ^ 2 + 2 ^ 2) * (2 * 2 ^ 6 + 2 ^ 6) := by
              iterate 3 apply mul_le_mul
              . rfl
              . omega
              . norm_num
              . norm_num
              . nlinarith only [show 2 ≤ b by omega]
              . positivity
              . positivity
              . apply add_le_add
                . rw [mul_le_mul_left (by norm_num)]
                  apply pow_le_pow (by omega) (by omega) (by rfl)
                . rfl
              . positivity
              . positivity
            _ > n := by
              omega
        absurd habsurd
        exact lt_irrefl n
      -- Contradictory with our assumption that b = 2.
      omega
    -- Now show that n ≥ (c + 1)(c² + 1)(2c⁶ + 1).
    have h₄ : n ≥ (c + 1) * (c ^ 2 + 1) * (3 * c ^ 6 + 1) := by
      calc
        n = a * (a + b + c + d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a ^ 6 + 2 * b ^ 6 + 3 * c ^ 6 + 4 * d ^ 6) := h₀.symm
        _ ≥ 1 * (1 + c) * (1 ^ 2 + c ^ 2) * (1 ^ 6 + 3 * c ^ 6) := by
          iterate 3 apply mul_le_mul
          . omega
          . omega
          . positivity
          . positivity
          . nlinarith only [ha']
          . positivity
          . positivity
          . linarith only [ha'', show 0 ≤ b ^ 6 by positivity, show 0 ≤ d ^ 6 by positivity]
          . positivity
          . positivity
        _ = (c + 1) * (c ^ 2 + 1) * (3 * c ^ 6 + 1) := by
          ring
    -- We get c ≤ 2.
    have h₅ : c ≤ 2 := by
      by_contra!
      -- Supose c ≥ 3, then n > 9999, contradiction.
      have habsurd : n > n := by
        calc
          n ≥ (c + 1) * (c ^ 2 + 1) * (3 * c ^ 6 + 1) := h₄
          _ ≥ (3 + 1) * (3 ^ 2 + 1) * (3 * 3 ^ 6 + 1) := by
            iterate 2 apply mul_le_mul
            . omega
            . nlinarith only [show 3 ≤ c by omega]
            . positivity
            . positivity
            . apply add_le_add
              . rw [mul_le_mul_left (by norm_num)]
                apply pow_le_pow (by omega) (by omega) (by rfl)
              . rfl
            . positivity
            . positivity
          _ > n := by
            omega
      absurd habsurd
      exact lt_irrefl n
    -- We further shows that c < 2.
    have h₆ : c < 2 := by
      by_contra!
      replace h₅ : c = 2 := by
        omega
      clear this
      -- Assume c = 2, then n ≥ 2985, hence a ≥ 2.
      have h₇ : a ≥ 2 := by
        by_contra!
        have habsurd : n > n := by
          calc
            n ≥ (c + 1) * (c ^ 2 + 1) * (3 * c ^ 6 + 1) := h₄
            _ ≥ (2 + 1) * (2 ^ 2 + 1) * (3 * 2 ^ 6 + 1) := by
              iterate 2 apply mul_le_mul
              . omega
              . nlinarith only [show 2 ≤ c by omega]
              . positivity
              . positivity
              . apply add_le_add
                . rw [mul_le_mul_left (by norm_num)]
                  apply pow_le_pow (by omega) (by omega) (by rfl)
                . rfl
              . positivity
              . positivity
            _ > n := by
              omega
        absurd habsurd
        exact lt_irrefl n
      -- Since a ≥ 2, we have c ≤ 1.
      have h₈ : c ≤ 1 := by
        by_contra!
        -- Suppose c ≥ 2, then n > 9999, contradiction.
        have habsurd : n > n := by
          calc
            n = a * (a + b + c + d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a ^ 6 + 2 * b ^ 6 + 3 * c ^ 6 + 4 * d ^ 6) := h₀.symm
            _ ≥ 2 * (2 + c) * (2 ^ 2 + c ^ 2) * (2 ^ 6 + 3 * c ^ 6) := by
              iterate 3 apply mul_le_mul
              . omega
              . omega
              . positivity
              . positivity
              . linarith only [show 2 ^ 2 ≤ a ^ 2 by nlinarith only [h₇], show 0 ≤ b ^ 2 by positivity, show 0 ≤ d ^ 2 by positivity]
              . positivity
              . positivity
              . linarith only [show 2 ^ 6 ≤ a ^ 6 by nlinarith only [show 2 ^ 2 ≤ a ^ 2 by nlinarith only [h₇], show 2 ^ 4 ≤ a ^ 4 by nlinarith only [show 2 ^ 2 ≤ a ^ 2 by nlinarith only [h₇]]], show 0 ≤ b ^ 6 by positivity, show 0 ≤ d ^ 6 by positivity]
              . positivity
              . positivity
            _ = 2 * (c + 2) * (c ^ 2 + 2 ^ 2) * (3 * c ^ 6 + 2 ^ 6) := by ring
            _ ≥ 2 * (2 + 2) * (2 ^ 2 + 2 ^ 2) * (3 * 2 ^ 6 + 2 ^ 6) := by
              iterate 3 apply mul_le_mul
              . rfl
              . omega
              . norm_num
              . norm_num
              . nlinarith only [show 2 ≤ c by omega]
              . positivity
              . positivity
              . apply add_le_add
                . rw [mul_le_mul_left (by norm_num)]
                  apply pow_le_pow (by omega) (by omega) (by rfl)
                . rfl
              . positivity
              . positivity
            _ > n := by
              omega
        absurd habsurd
        exact lt_irrefl n
      -- Contradictory with our assumption that c = 2.
      omega
    -- Now show that n ≥ (d + 1)(d² + 1)(4d⁶ + 1).
    have h₉ : n ≥ (d + 1) * (d ^ 2 + 1) * (4 * d ^ 6 + 1) := by
      calc
        n = a * (a + b + c + d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a ^ 6 + 2 * b ^ 6 + 3 * c ^ 6 + 4 * d ^ 6) := h₀.symm
        _ ≥ 1 * (1 + d) * (1 ^ 2 + d ^ 2) * (1 ^ 6 + 4 * d ^ 6) := by
          iterate 3 apply mul_le_mul
          . omega
          . omega
          . positivity
          . positivity
          . nlinarith only [ha']
          . positivity
          . positivity
          . linarith only [ha'', show 0 ≤ b ^ 6 by positivity, show 0 ≤ c ^ 6 by positivity]
          . positivity
          . positivity
        _ = (d + 1) * (d ^ 2 + 1) * (4 * d ^ 6 + 1) := by
          ring
    -- We get d ≤ 2.
    have h₁₀ : d ≤ 2 := by
      by_contra!
      -- Supose d ≥ 3, then n > 9999, contradiction.
      have habsurd : n > n := by
        calc
          n ≥ (d + 1) * (d ^ 2 + 1) * (4 * d ^ 6 + 1) := h₉
          _ ≥ (3 + 1) * (3 ^ 2 + 1) * (4 * 3 ^ 6 + 1) := by
            iterate 2 apply mul_le_mul
            . omega
            . nlinarith only [show 3 ≤ d by omega]
            . positivity
            . positivity
            . apply add_le_add
              . rw [mul_le_mul_left (by norm_num)]
                apply pow_le_pow (by omega) (by omega) (by rfl)
              . rfl
            . positivity
            . positivity
          _ > n := by
            omega
      absurd habsurd
      exact lt_irrefl n
    -- We further shows that d < 2.
    have h₁₁ : d < 2 := by
      by_contra!
      replace h₁₀ : d = 2 := by
        omega
      clear this
      -- Assume d = 2, then n ≥ 3990, hence a ≥ 3.
      have h₁₂ : a ≥ 3 := by
        by_contra!
        have habsurd : n > n := by
          calc
            n ≥ (d + 1) * (d ^ 2 + 1) * (4 * d ^ 6 + 1) := h₉
            _ ≥ (2 + 1) * (2 ^ 2 + 1) * (4 * 2 ^ 6 + 1) := by
              iterate 2 apply mul_le_mul
              . omega
              . nlinarith only [show 2 ≤ d by omega]
              . positivity
              . positivity
              . apply add_le_add
                . rw [mul_le_mul_left (by norm_num)]
                  apply pow_le_pow (by omega) (by omega) (by rfl)
                . rfl
              . positivity
              . positivity
            _ > n := by
              omega
        absurd habsurd
        exact lt_irrefl n
      -- Since a ≥ 3, we have d ≤ 1.
      have h₁₃ : d ≤ 1 := by
        by_contra!
        -- Suppose d ≥ 2, then n > 9999, contradiction.
        have habsurd : n > n := by
          calc
            n = a * (a + b + c + d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (a ^ 6 + 2 * b ^ 6 + 3 * c ^ 6 + 4 * d ^ 6) := h₀.symm
            _ ≥ 3 * (3 + d) * (3 ^ 2 + d ^ 2) * (3 ^ 6 + 4 * d ^ 6) := by
              iterate 3 apply mul_le_mul
              . omega
              . omega
              . positivity
              . positivity
              . linarith only [show 3 ^ 2 ≤ a ^ 2 by nlinarith only [h₁₂], show 0 ≤ b ^ 2 by positivity, show 0 ≤ c ^ 2 by positivity]
              . positivity
              . positivity
              . linarith only [show 3 ^ 6 ≤ a ^ 6 by nlinarith only [show 3 ^ 2 ≤ a ^ 2 by nlinarith only [h₁₂], show 3 ^ 4 ≤ a ^ 4 by nlinarith only [show 3 ^ 2 ≤ a ^ 2 by nlinarith only [h₁₂]]], show 0 ≤ b ^ 6 by positivity, show 0 ≤ c ^ 6 by positivity]
              . positivity
              . positivity
            _ = 3 * (d + 3) * (d ^ 2 + 3 ^ 2) * (4 * d ^ 6 + 3 ^ 6) := by ring
            _ ≥ 3 * (2 + 3) * (2 ^ 2 + 3 ^ 2) * (4 * 2 ^ 6 + 3 ^ 6) := by
              iterate 3 apply mul_le_mul
              . rfl
              . omega
              . norm_num
              . norm_num
              . nlinarith only [show 2 ≤ d by omega]
              . positivity
              . positivity
              . apply add_le_add
                . rw [mul_le_mul_left (by norm_num)]
                  apply pow_le_pow (by omega) (by omega) (by rfl)
                . rfl
              . positivity
              . positivity
            _ > n := by
              omega
        absurd habsurd
        exact lt_irrefl n
      -- Contradictory with our assumption that d = 2.
      omega
    -- Check cases of b, c and d.
    simp
    interval_cases b
    <;> interval_cases c
      <;> interval_cases d
        <;> simp [hn] at h₀
    . -- Case (b, c, d) = (0, 0, 0).
      ring_nf at h₀
      -- Now a¹⁰ = 1000a has no solution.
      interval_cases a
      <;> norm_num at h₀
    . -- Case (b, c, d) = (0, 0, 1).
      interval_cases a
      <;> norm_num at h₀
    . -- Case (b, c, d) = (0, 1, 0).
      interval_cases a
      <;> norm_num at h₀
      -- The only possible case is a = 2.
      simp [hn]
    . -- Case (b, c, d) = (0, 1, 1).
      interval_cases a
      <;> norm_num at h₀
    . -- Case (b, c, d) = (1, 0, 0).
      interval_cases a
      <;> norm_num at h₀
    . -- Case (b, c, d) = (1, 0, 1).
      interval_cases a
      <;> norm_num at h₀
    . -- Case (b, c, d) = (1, 1, 0).
      interval_cases a
      <;> norm_num at h₀
    . -- Case (b, c, d) = (1, 1, 1).
      interval_cases a
      <;> norm_num at h₀
  . -- Check that 2010 satisfies the equation.
    intro h
    simp at h
    rw [Set.mem_setOf]
    use 2, 0, 1, 0
    norm_num
    exact ⟨h.symm, h⟩
