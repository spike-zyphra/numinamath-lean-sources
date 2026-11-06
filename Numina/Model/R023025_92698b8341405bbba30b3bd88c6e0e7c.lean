import Mathlib

theorem algebra_253198 (a : ℝ) :
    (∑ i ∈ Finset.range 1981, (-a)^i) - a^1981 / (1 + a) = 5 ↔ a = -4 / 5 := by
  constructor
  · -- Assume that the expression equals 5, prove that a = -4 / 5
    intro h 
    have h1 : a ≠ -1 := by 
      by_contra h1
      have h1 : a = -1 := by linarith 
      rw [h1] at h 
      norm_num at h 
    -- Prove the formula for the sum of a finite geometric series
    have h2 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (-a)^i = (1 - (-a)^n) / (1 + a) := by
      intro n 
      induction n with 
      | zero =>
        simp 
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp [(show 1 + a ≠ 0 by
          intro h'
          apply h1
          linarith
          )]
        ring
    -- Apply the formula for n = 1981
    have h3 : (∑ i ∈ Finset.range 1981, (-a)^i) = (1 - (-a)^1981) / (1 + a) := h2 1981 
    rw [h3] at h
    -- Simplify the expression to 1 / (1 + a)
    have h4 : (1 - (-a)^1981) / (1 + a) - a^1981 / (1 + a) = 1 / (1 + a) := by 
      have h5 : (1 - (-a)^1981) / (1 + a) - a^1981 / (1 + a) = ( (1 - (-a)^1981) - a^1981 ) / (1 + a) := by 
        ring 
      rw [h5]
      have h6 : (1 - (-a)^1981) - a^1981 = 1 := by
        have h7 : (-a) ^ 1981 = - a ^ 1981 := by
          have h8 : 1981 % 2 = 1 := by norm_num 
          have h9 : ∀ (k : ℕ), (-a) ^ (2 * k + 1) = - a ^ (2 * k + 1) := by
            intro k
            induction k with 
            | zero =>
              simp 
            | succ k ihk => 
              simp [pow_succ, pow_mul] at ihk ⊢ 
              <;> nlinarith 
          specialize h9 (1981 / 2)
          norm_num at h9 ⊢ 
          all_goals linarith
        rw [h7]
        ring 
      rw [h6]
      <;> field_simp [(show 1 + a ≠ 0 by
        intro h'
        apply h1
        linarith
        )]
    -- Apply the simplification to the hypothesis h
    rw [h4] at h 
    -- Solve for a
    have h5 : 1 / (1 + a) = 5 := h 
    have h6 : 1 + a = 1 / 5 := by
      have h7 : (1 + a) ≠ 0 := by
        intro h7
        apply h1
        linarith 
      field_simp [h7] at h5 
      linarith 
    have h7 : a = -4 / 5 := by
      nlinarith 
    linarith 
  · -- Assume that a = -4 / 5, prove that the expression equals 5
    intro h 
    rw [h]
    have h1 : ∑ i ∈ Finset.range 1981, (- (-4 / (5 : ℝ)) )^i = (1 - (- (-4 / (5 : ℝ)) )^1981 ) / (1 + (-4 / (5 : ℝ)) ) := by
      have h2 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (- (-4 / (5 : ℝ)) )^i = (1 - (- (-4 / (5 : ℝ)) )^n ) / (1 + (-4 / (5 : ℝ)) ) := by
        intro n
        induction n with
        | zero => 
          simp 
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          field_simp [(show (1 + (-4 / (5 : ℝ)) ) ≠ 0 by norm_num)]
          ring
      specialize h2 1981 
      simpa using h2 
    rw [h1] 
    norm_num