import Mathlib

theorem algebra_323405 (m : ℝ) :
    ∃ x : ℝ, Real.sin x ^ 2 + Real.cos x + m = 0 ↔ -5 / 4 ≤ m ∧ m ≤ 1 := by
  by_cases h : -5 / 4 ≤ m ∧ m ≤ 1
  · -- If m ∈ [-5/4, 1], we construct x such that the equation holds
    have h1 : -5 / 4 ≤ m := h.1
    have h2 : m ≤ 1 := h.2
    use Real.arccos ((1 - Real.sqrt (5 + 4 * m)) / 2)
    constructor
    · -- Assume the equation holds, prove m ∈ [-5/4, 1]
      intro h_eq
      exact h
    · -- Assume m ∈ [-5/4, 1], prove the equation holds
      intro h_eq
      have h3 : 0 ≤ 5 + 4 * m := by linarith
      have h4 : Real.sin (Real.arccos ((1 - Real.sqrt (5 + 4 * m)) / 2)) ^ 2 = 1 - Real.cos (Real.arccos ((1 - Real.sqrt (5 + 4 * m)) / 2)) ^ 2 := by
        rw [Real.sin_sq]
      have h5 : Real.cos (Real.arccos ((1 - Real.sqrt (5 + 4 * m)) / 2)) = (1 - Real.sqrt (5 + 4 * m)) / 2 := by
        apply Real.cos_arccos
        · -- Show -1 ≤ (1 - Real.sqrt (5 + 4 * m)) / 2
          nlinarith [Real.sqrt_nonneg (5 + 4 * m), Real.sq_sqrt (show (0 : ℝ) ≤ 5 + 4 * m by linarith)]
        · -- Show (1 - Real.sqrt (5 + 4 * m)) / 2 ≤ 1
          nlinarith [Real.sqrt_nonneg (5 + 4 * m), Real.sq_sqrt (show (0 : ℝ) ≤ 5 + 4 * m by linarith)]
      rw [h5] at h4
      nlinarith [Real.sqrt_nonneg (5 + 4 * m), Real.sq_sqrt (show (0 : ℝ) ≤ 5 + 4 * m by linarith), sq_nonneg (Real.sqrt (5 + 4 * m) - 3 / 2)]
  · -- If m ∉ [-5/4, 1], show that the biconditional is false
    push_neg at h
    use 0
    constructor
    · -- Assume the equation holds, prove m ∈ [-5/4, 1]
      intro h_eq
      -- The equation with x = 0 becomes 1 + m = 0, so m = -1
      -- Check if m = -1 satisfies m ∈ [-5/4, 1]
      have h_m : m = -1 := by
        have : Real.sin 0 ^ 2 + Real.cos 0 + m = 0 := by
          simpa using h_eq
        simp at this
        linarith
      -- Since m = -1, we have -5/4 ≤ -1 and -1 ≤ 1, so m ∈ [-5/4, 1]
      have h1 : -5 / 4 ≤ m := by
        linarith [h_m]
      have h2 : m ≤ 1 := by
        linarith [h_m]
      constructor <;> linarith
    · -- Assume m ∈ [-5/4, 1], prove the equation holds
      intro h_eq
      -- This is a contradiction since we assumed m ∉ [-5/4, 1]
      have h13 : -5/4 ≤ m := h_eq.1
      have h14 : m ≤ 1 := h_eq.2
      have h15 : m > 1 := by 
        apply h 
        tauto 
      linarith