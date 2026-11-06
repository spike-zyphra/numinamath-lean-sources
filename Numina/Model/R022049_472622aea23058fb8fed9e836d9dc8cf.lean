import Mathlib

theorem algebra_324460 {b c : ℝ} (f : ℝ → ℝ)
    (h₀ : ∀ x, x ≥ 0 → f x = x ^ 2 + b * x + c)
    (h₁ : ∀ x, x < 0 → f x = -2)
    (h₂ : f 4 = f 0) (h₃ : f 1 = -1) :
    {x | f x = x}.encard = 3 := by

  have eq1 : f 4 = 4 ^ 2 + b * 4 + c := by
    apply h₀
    norm_num

  have eq2 : f 0 = 0 ^ 2 + b * 0 + c := by
    apply h₀
    norm_num

  have h4 : b = -4 := by
    rw [eq1, eq2] at h₂
    linarith

  have eq3 : f 1 = 1 ^ 2 + b * 1 + c := by
    apply h₀
    norm_num

  have h5 : c = 2 := by
    rw [eq3] at h₃
    rw [h4] at h₃
    linarith

  have h8 : {x | f x = x} = { (5 + Real.sqrt 17) / 2, (5 - Real.sqrt 17) / 2, -2 } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Proof that if f x = x then x ∈ { (5 ± Real.sqrt 17) / 2, -2 }
      intro hx
      by_cases h : x ≥ 0
      · -- Assume x ≥ 0
        have h9 : f x = x ^ 2 + b * x + c := by
          apply h₀ x h
        rw [h9] at hx
        rw [h4, h5] at hx
        have h10 : x ^ 2 + (-4) * x + 2 = x := by linarith
        have h11 : x ^ 2 + (-4) * x + 2 - x = 0 := by linarith
        have h12 : (x - (5 + Real.sqrt 17) / 2) * (x - (5 - Real.sqrt 17) / 2) = 0 := by
          nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (17 : ℝ) ≥ 0 by norm_num)]
        cases' (mul_eq_zero.1 h12) with h13 h14
        · -- First case: x - (5 + Real.sqrt 17) / 2 = 0
          left
          linarith
        · -- Second case: x - (5 - Real.sqrt 17) / 2 = 0
          right
          left
          linarith
      · -- Assume x < 0
        have h15 : x < 0 := by linarith
        have h10 : f x = -2 := by
          apply h₁ x h15
        rw [h10] at hx
        right
        right
        linarith
    · -- Proof that each x in { (5 ± Real.sqrt 17)/2, -2 } is a solution.
      rintro (h | h | h)
      · -- First case: x = (5 + Real.sqrt 17) / 2
        have h17 : x ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (17 : ℝ) ≥ 0 by norm_num)]
        have h16 : f x = x ^ 2 + b * x + c := by
          apply h₀
          exact h17
        rw [h16, h4, h5]
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (17 : ℝ) ≥ 0 by norm_num)]
      · -- Second case: x = (5 - Real.sqrt 17) / 2
        have h17 : x ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (17 : ℝ) ≥ 0 by norm_num)]
        have h16 : f x = x ^ 2 + b * x + c := by
          apply h₀
          exact h17
        rw [h16, h4, h5]
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (17 : ℝ) ≥ 0 by norm_num)]
      · -- Third case: x = -2
        have h17 : x < 0 := by linarith
        have h16 : f x = -2 := by
          apply h₁
          exact h17
        rw [h16]
        linarith

  rw [h8]
  have h9 : ( (5 + Real.sqrt 17) / 2 : ℝ ) ≠ ( (5 - Real.sqrt 17) / 2 : ℝ ) := by
    intro h
    nlinarith [Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (17 : ℝ) ≥ 0 by norm_num)]
  have h10 : ( (5 + Real.sqrt 17) / 2 : ℝ ) ≠ ( -2 : ℝ ) := by
    intro h
    nlinarith [Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (17 : ℝ) ≥ 0 by norm_num)]
  have h11 : ( (5 - Real.sqrt 17) / 2 : ℝ ) ≠ ( -2 : ℝ ) := by
    intro h
    nlinarith [Real.sqrt_pos.mpr (show (17 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (17 : ℝ) ≥ 0 by norm_num)]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton, h9, h10, h11]
  <;> norm_num