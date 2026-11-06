import Mathlib

/- 9.4. It is known that the values of the quadratic trinomial $a x^{2}+b x+c$ on the interval $[-1,1]$ do not exceed 1 in absolute value. Find the maximum possible value of the sum $|a|+|b|+|c|$. Answer. 3. -/
theorem algebra_250144 :
    IsGreatest {s : ℝ | ∃ a b c : ℝ, s = |a| + |b| + |c| ∧ ∀ x ∈ Set.Icc (-1) 1, |a * x ^ 2 + b * x + c| ≤ 1} 3 := by
  simp only [IsGreatest, Set.mem_Icc, and_imp, Set.mem_setOf_eq, upperBounds, forall_exists_index]
  constructor
  -- Show that 2 * x^2 - 1 satisfies the condition |2 * x^2 - 1| ≤ 1 for all x ∈ [-1, 1]
  -- abd |2| + |0| + |-1| = 3.
  · use 2, 0, -1
    norm_num
    intro x hx1 hx2
    rw [abs_le]
    constructor <;> nlinarith
  -- Assume that |a * x^2 + b * x + c| ≤ 1 for all x ∈ [-1, 1] and
  -- show that |a| + |b| + |c| ≤ 3.
  intro s a b c hs h
  -- Without loss of generality, assume that 0 ≤ a.
  wlog ha0 : 0 ≤ a generalizing a b c
  · apply this (-a) (-b) (-c)
    · simp only [abs_neg, hs]
    · intro x hx1 hx2
      rw [show -a * x^2 + -b * x + -c = -(a * x^2 + b * x + c) by ring, abs_neg]
      exact h x hx1 hx2
    · linarith
  -- From |a * x ^ 2 + b * x + c| ≤ 1 for x ∈ [-1, 1], we get
  -- |c| ≤ 1, |a + b + c| ≤ 1, and |a - b + c| ≤ 1.
  have hn1 := h (-1) (by norm_num) (by norm_num)
  have h0 := h 0 (by norm_num) (by norm_num)
  have h1 := h 1 (by norm_num) (by norm_num)
  simp at h0 h1 hn1
  rw [hs, abs_of_nonneg ha0]
  rw [abs_le] at h1 hn1 h0
  -- Consider two cases: 0 ≤ b or b < 0.
  by_cases hb0 : 0 ≤ b
  · rw [abs_of_nonneg hb0]
    -- Assume that 0 ≤ b.
    -- Consider two cases: 0 ≤ c or c < 0.
    by_cases hc0 : 0 ≤ c
    · rw [abs_of_nonneg hc0]
      -- If 0 ≤ c then |a| + |b| + |c| = a + b + c ≤ 1 < 3.
      linarith
    · simp at hc0
      -- If c < 0 then |a| + |b| + |c| = a + b - c = (a + b + c) - 2 * c ≤ 1 + 2 = 3.
      rw [abs_of_neg hc0]
      linarith
  · simp at hb0
    rw [abs_of_neg hb0]
    -- Assume that b < 0.
    -- Consider two cases: 0 ≤ c or c < 0.
    by_cases hc0 : 0 ≤ c
    · rw [abs_of_nonneg hc0]
      -- If 0 ≤ c then |a| + |b| + |c| = a - b + c ≤ 1 < 3.
      linarith
    · simp at hc0
      -- If c < 0 then |a| + |b| + |c| = a - b - c = (a - b + c) - 2 * c ≤ 1 + 2 = 3.
      rw [abs_of_neg hc0]
      linarith