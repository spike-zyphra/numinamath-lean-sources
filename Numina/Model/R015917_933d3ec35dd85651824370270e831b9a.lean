import Mathlib

theorem number_theory_8741 :
    IsLeast {x : ℕ | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = a^2 + b^2 + c^2 ∧
      ∃ n : ℕ, n > 0 ∧ √(a + b) = n ∧ √(b + c) = n + 1 ∧ √(c + a) = n + 2} 1297 := by 
  constructor
  · -- Prove that 1297 is in the set 
    use 19, 6, 30
    constructor
    · norm_num -- a > 0
    constructor
    · norm_num -- b > 0
    constructor
    · norm_num -- c > 0
    constructor
    · norm_num -- x = a^2 + b^2 + c^2
    use 5
    constructor
    · norm_num -- n > 0
    constructor
    · -- √(a + b) = n
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    constructor
    · -- √(b + c) = n + 1
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    · -- √(c + a) = n + 2
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  · -- Prove that 1297 is the least element in the set 
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h_eq, n, hn, h1, h2, h3⟩
    have h1' : (a + b : ℝ) = (n : ℝ) ^ 2 := by
      calc
        (a + b : ℝ) = (√(a + b) : ℝ) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (n : ℝ) ^ 2 := by rw [h1]
    have h2' : (b + c : ℝ) = ((n + 1 : ℝ) ) ^ 2 := by
      calc
        (b + c : ℝ) = (√(b + c) : ℝ) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = ((n + 1 : ℝ) ) ^ 2 := by rw [h2]
    have h3' : (c + a : ℝ) = ((n + 2 : ℝ) ) ^ 2 := by
      calc
        (c + a : ℝ) = (√(c + a) : ℝ) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = ((n + 2 : ℝ) ) ^ 2 := by rw [h3]
    have eq1 : a + b = n ^ 2 := by
      exact_mod_cast h1'
    have eq2 : b + c = (n + 1) ^ 2 := by
      exact_mod_cast h2'
    have eq3 : c + a = (n + 2) ^ 2 := by
      exact_mod_cast h3'
    by_contra h
    push_neg at h
    have h4 : x < 1297 := h
    rw [h_eq] at h4
    have eq4 : n ≤ 10 := by
      nlinarith [sq_nonneg (a - 19 : ℝ), sq_nonneg (b - 6 : ℝ), sq_nonneg (c - 30 : ℝ)]
    interval_cases n <;> try { 
      omega
    }
    all_goals
      nlinarith