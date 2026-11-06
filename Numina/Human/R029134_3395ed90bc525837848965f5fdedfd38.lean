import Mathlib

/- Problem 2. Determine all pairs $(a, b)$ of natural numbers for which the fractions


$$

\frac{3 a+8 b+2}{10 a+2 b+1} \quad \text { and } \quad \frac{8 a+b+3}{2 a+7 b+3}

$$


represent, simultaneously, natural numbers. -/
theorem number_theory_105817 (a b : ℕ) :
    (∃ m n : ℕ, (3 * a + 8 * b + 2: ℚ) / (10 * a + 2 * b + 1) = m ∧
    (8 * a + b + 3: ℚ) / (2 * a + 7 * b + 3) = n) ↔ a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  constructor
  . rintro ⟨m, n, hm, hn⟩
    -- first of all 1 <= m and 1 <= n as the terms are positive
    have hm_lb : 0 < m := by qify; rw [← hm]; positivity
    replace hm_lb : 1 <= m := by omega
    have hn_lb : 0 < n := by qify; rw [← hn]; positivity
    replace hn_lb : 1 <= n := by omega
    -- next 1 <= m and 1 <= n means the numerators are >= denominators
    have h₁ : 10 * a  + 2 * b + 1 ≤ 3 * a + 8 * b + 2 := by
      have : (10 * a  + 2 * b + 1) * 1 ≤ (10 * a  + 2 * b + 1) * m := by gcongr
      qify at this ⊢
      rw [show (10 * a  + 2 * b + 1: ℚ) * m = 3 * a + 8 * b + 2 by rw [← hm]; field_simp] at this
      linarith
    have h₂ : 2 * a + 7 * b + 3 ≤ 8 * a + b + 3 := by
      have : (2 * a + 7 * b + 3) * 1 ≤ (2 * a + 7 * b + 3) * n := by gcongr
      qify at this ⊢
      rw [show (2 * a + 7 * b + 3: ℚ) * n = 8 * a + b + 3 by rw [← hn]; field_simp] at this
      linarith
    -- from the two inequalities we easily get a <= 1
    have : a ≤ 1 := by omega
    -- trying out a = 0, a = 1, we see in both cases b = 0 and  b = 1 can be determined
    interval_cases a <;> (simp; omega)
    -- trying out (a, b) = (0, 0) or (1, 1) we see that m, n are natural numbers (2, 1) or (1, 1)
  . rintro h
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
    . use 2, 1
      norm_num
    . use 1, 1
      norm_num