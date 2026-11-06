import Mathlib

theorem algebra_297420 (n : ℕ) (x : ℝ) (h₀ : n > 0) (h₁ : ∑ i ∈ Finset.range 3, |(Nat.choose n i) * (x^(18*x) - 2)^i| = 73)
    (h₂ : (Nat.choose n 1) * (x^(18*x) - 2)^1 = -160000) :
    x = 10 ∨ x = 1 / 10 := by
  have h3 : n ≥ 1 := by linarith
  have eq1 : ∑ i in Finset.range 3, |(Nat.choose n i) * (x^(18*x) - 2)^i| =
      |(Nat.choose n 0) * (x^(18*x) - 2)^0| +
      |(Nat.choose n 1) * (x^(18*x) - 2)^1| +
      |(Nat.choose n 2) * (x^(18*x) - 2)^2| := by
    simp [Finset.sum_range_succ]
    all_goals try { linarith }
  rw [eq1] at h₁
  -- Equation h₁ computed
  -- First term: $1$ 
  have eq3 : |(Nat.choose n 0) * (x^(18*x) - 2)^0| = 1 := by
    simp [Nat.choose_zero_right]
    all_goals try { linarith }
    <;> try { norm_num }
  have eq4 : |(Nat.choose n 1) * (x^(18*x) - 2)^1| = 160000 := by
    have eq8 : (Nat.choose n 1) * (x^(18*x) - 2)^1 = (-160000 : ℝ) := by
      exact_mod_cast h₂
    have h7 : |(Nat.choose n 1 : ℝ) * (x^(18*x) - 2)^1| = |(-160000 : ℝ)| := by
      rw [show (Nat.choose n 1 : ℝ) * (x^(18*x) - 2) ^ 1 = (-160000 : ℝ) by linarith [eq8] ]
      <;> try { tauto }
      all_goals try { try { tauto } }
    rw [h7]
    all_goals norm_num [abs_of_nonneg, abs_of_nonpos]
    all_goals try { tauto }
    all_goals try { nlinarith }
  -- Substitute First and Second Term into h₁
  rw [eq3, eq4] at h₁
  -- From h₁: reduce to get the value of the third term
  -- Equation of Third term: $73 - 1 - 160000$ 
  have h4 : |(Nat.choose n 2 : ℝ) * (x^(18*x) - 2) ^ (2 : ℕ)| ≥ 0 := by
    apply abs_nonneg
  have h5 : |(Nat.choose n 2 : ℝ) * (x^(18*x) - 2) ^ (2 : ℕ)| = (73 : ℝ) - 1 - 160000 := by 
    linarith 
  have h6 : (73 : ℝ) - 1 - 160000 ≤ (0 : ℝ) := by 
    norm_num 
  have h7 : |(Nat.choose n 2 : ℝ) * (x^(18*x) - 2) ^ (2 : ℕ)| = (73 : ℝ) - 1 - 160000 := h5
  have h8 : (73 : ℝ) - 1 - 160000 < (0 : ℝ) := by
    norm_num
  -- Thus takes the value of being negative - contradiction.
  have h9 : |(Nat.choose n 2 : ℝ) * (x^(18*x) - 2) ^ (2 : ℕ)| ≥ (0 : ℝ) := by 
    apply abs_nonneg 
  linarith [show (73 : ℝ) - 1 - 160000 < (0 : ℝ) from by norm_num, show
    |(Nat.choose n 2 : ℝ) * (x^(18*x) - 2) ^ (2 : ℕ)| ≥ (0 : ℝ) by apply abs_nonneg
  ]