import Mathlib

theorem algebra_310958 {f : ℝ → ℝ} (hf : f = fun x => x^2 - 3 * x + 2) :
    Set.ncard {x | f (f x) = 0} = 4 := by
  have h1 : {x | f (f x) = 0} = { (3 + Real.sqrt 5) / 2, (3 - Real.sqrt 5) / 2, (0 : ℝ), (3 : ℝ) } := by
    ext x
    simp [hf]
    constructor
    · -- Assume f (f x) = 0, prove x ∈ { (3 ±√5)/2, 0, 3 }
      intro h
      have h2 : (x ^ 2 - 3 * x + 2) ^ 2 - 3 * (x ^ 2 - 3 * x + 2) + 2 = 0 := by
        nlinarith
      have h3 : (x ^ 2 - 3 * x + 2 - 2) * (x ^ 2 - 3 * x + 2 - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h3) with h4 h5
      · -- Case where f(x) = 2
        have h6 : x ^ 2 - 3 * x = 0 := by
          nlinarith
        have h7 : x * (x - 3) = 0 := by
          linarith [h6]
        cases' (mul_eq_zero.1 h7) with h8 h9
        · -- Case x = 0
          right
          right
          left
          linarith
        · -- Case x = 3
          right
          right
          right
          linarith
      · -- Case where f(x) = 1
        have h8 : x ^ 2 - 3 * x + 1 = 0 := by
          nlinarith
        -- Solving quadratic gives x = (3 ±√5)/2
        have h9 : (x - (3 + Real.sqrt 5) / 2) * (x - (3 - Real.sqrt 5) / 2) = 0 := by
          nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
        cases' (mul_eq_zero.1 h9) with h10 h11
        · -- Case x = (3 + √5)/2
          left
          linarith
        · -- Case x = (3 - √5)/2
          right
          left
          linarith
    · -- Assume x ∈ { (3 ±√5)/2, 0, 3 }, prove f(f(x)) = 0
      rintro (h | h | h | h)
      · -- Case x = (3 + √5)/2
        rw [h]
        nlinarith [ Real.sqrt_pos.2 (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      · -- Case x = (3 - √5)/2
        rw [h]
        nlinarith [ Real.sqrt_pos.2 (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      · -- Case x = 0
        rw [h]
        norm_num
      · -- Case x = 3
        rw [h]
        norm_num
  rw [h1]
  have h2 : 0 < Real.sqrt 5 := by
    apply Real.sqrt_pos.mpr
    norm_num
  have h3 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h4 : ( (3 + Real.sqrt 5) / 2 : ℝ ) ≠ ( (3 - Real.sqrt 5) / 2 : ℝ ) := by
    intro h
    have : Real.sqrt 5 = 0 := by linarith
    linarith [h2, this]
  have h5 : ( (3 + Real.sqrt 5) / 2 : ℝ ) ≠ ( 0 : ℝ ) := by
    intro h
    nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (5 : ℝ) by norm_num), h2]
  have h6 : ( (3 + Real.sqrt 5) / 2 : ℝ ) ≠ ( 3 : ℝ ) := by
    intro h
    nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (5 : ℝ) by norm_num), h2, h3]
  have h7 : ( (3 - Real.sqrt 5) / 2 : ℝ ) ≠ ( 0 : ℝ ) := by
    intro h
    have : 3 - Real.sqrt 5 = 0 := by linarith
    nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (5 : ℝ) by norm_num), h2, h3]
  have h8 : ( (3 - Real.sqrt 5) / 2 : ℝ ) ≠ ( 3 : ℝ ) := by
    intro h
    nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (5 : ℝ) by norm_num), h2, h3]
  have h9 : ( (0 : ℝ ) ) ≠ ( (3 : ℝ ) ) := by
    norm_num
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset_insert, Set.toFinset_singleton, Finset.card_insert_of_not_mem, Finset.card_singleton, h4, h5, h6, h7, h8, h9]