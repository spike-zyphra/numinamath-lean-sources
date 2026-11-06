import Mathlib

/- 4. All values of the quadratic trinomial $f(x)=a x^{2}+b x+c$ on the interval $[0 ; 2]$ do not exceed 1 in absolute value. What is the greatest value that the quantity $|a|+|b|+|c|$ can have under these conditions? For which function $f(x)$ is this value achieved? -/
theorem algebra_109776 :
    IsGreatest {s : ℝ | ∃ a b c : ℝ, s = |a| + |b| + |c| ∧ ∀ x ∈ Set.Icc 0 2, |a * x ^ 2 + b * x + c| ≤ 1} 7 := by
  simp only [IsGreatest, Set.mem_Icc, and_imp, Set.mem_setOf_eq, upperBounds, forall_exists_index]
  constructor
  · use 2, -4, 1
    -- Show that 2 * x^2 - 4 * x + 1 satisfies the condition
    -- |2 * x^2 - 4 * x + 1| ≤ 1 for all x ∈ [0, 2] and
    -- |2| + |-4| + |1| = 7.
    norm_num
    intro x hx1 hx2
    -- We have 2 * x^2 - 4 * x + 1 = 2 * (x - 1)^2 - 1.
    rw [show 2 * x ^ 2 + -(4 * x) + 1 = 2 * (x - 1)^2 - 1 by ring]
    rw [abs_le]
    constructor <;> nlinarith
  -- Assume that |a * x^2 + b * x + c| ≤ 1 for all x ∈ [0, 2] and
  -- show that |a| + |b| + |c| ≤ 7.
  intro s a b c hs h
  -- x = 0 implies |c| ≤ 1.
  have h0 := h 0 (by norm_num) (by norm_num)
  -- x = 1 implies |a + b + c| ≤ 1.
  have h1 := h 1 (by norm_num) (by norm_num)
  -- x = 2 implies |4 * a + 2 * b + c| ≤ 1.
  have h2 := h 2 (by norm_num) (by norm_num)
  simp at h0 h1
  rw [show a * 2 ^ 2 = 4 * a by ring, mul_comm b] at h2
  -- It is enough to show that |2 * a| ≤ 4 and |2 * b| ≤ 8.
  suffices |2 * a| ≤ 4 ∧ |2 * b| ≤ 8 by
    simp_rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num] at this
    linarith
  constructor
  · calc
      -- We have
      -- |2 * a| = |(4 * a + 2 * b + c) + (-2) * (a + b + c) + c|
      --         ≤ |4 * a + 2 * b + c| + |(-2) * (a + b + c)| + |c|
      --         ≤ 1 + 2 * 1 + 1 = 4.
      |2 * a| = |(4 * a + 2 * b + c) + (-2) * (a + b + c) + c| := by ring_nf
      _ ≤ |4 * a + 2 * b + c| + |(-2) * (a + b + c)| + |c| := by
        apply le_trans (abs_add _ _)
        gcongr
        apply abs_add
      _ ≤ 1 + 2 * 1 + 1 := by
        rw [abs_mul]
        gcongr
        norm_num
      _ = 4 := by norm_num
  · calc
      -- We have
      -- |2 * b| = |4 * (a + b + c) - (4 * a + 2 * b + c) - 3 * c|
      --         ≤ |4 * (a + b + c)| + |4 * a + 2 * b + c| + |3 * c|
      --         ≤ 4 * 1 + 1 + 3 * 1 = 8.
      |2 * b| = |4 * (a + b + c) - (4 * a + 2 * b + c) - 3 * c| := by ring_nf
      _ ≤ |4 * (a + b + c)| + |4 * a + 2 * b + c| + |3 * c| := by
        apply le_trans (abs_sub _ _)
        gcongr
        apply abs_sub
      _ ≤ 4 * 1 + 1 + 3 * 1 := by
        simp_rw [abs_mul]
        gcongr <;> norm_num
      _ = 8 := by norm_num