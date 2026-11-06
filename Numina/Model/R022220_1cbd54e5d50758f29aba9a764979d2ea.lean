import Mathlib

theorem algebra_134692 (a : ℝ) :
    (∃ x y z w : ℝ, x ≠ y ∧ y ≠ z ∧ z ≠ w ∧
      x^4 - a * x^2 + 1 = 0 ∧
      y^4 - a * y^2 + 1 = 0 ∧
      z^4 - a * z^2 + 1 = 0 ∧
      w^4 - a * w^2 + 1 = 0 ∧
      ∃ d : ℝ, y = x + d ∧ z = y + d ∧ w = z + d) ↔ a = 10 / 3 := by 
  constructor
  · -- Forward implication: if there are 4 roots in arithmetic progression, then a = 10/3
    rintro ⟨x, y, z, w, h1, h2, h3, hx, hy, hz, hw, ⟨d, h4, h5, h6⟩⟩ 
    have eq1 : y = x + d := by linarith 
    have eq2 : z = x + 2 * d := by 
      nlinarith [h4, h5, eq1]
    have eq3 : w = x + 3 * d := by 
      nlinarith [h5, h6, eq2]
    rw [eq1] at hy 
    rw [eq2] at hz 
    rw [eq3] at hw 
    have h7 : d ≠ 0 := by 
      intro h
      have h8 : x = y := by 
        nlinarith [h4, h] 
      contradiction 
    nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by
      by_contra h
      have h0 : x = 0 := by
        nlinarith 
      rw [h0] at hx 
      nlinarith 
    ), sq_pos_of_ne_zero h7, sq_nonneg (d * x), sq_nonneg ((x ^ 2 - 3) * d), sq_nonneg (x ^ 2 - 3), sq_nonneg (d ^ 2 - 4 / 9 * x ^ 2), sq_nonneg (x ^ 2 - (x + 3 * d) ^ 2)
    ]
  · -- Backward implication: if a = 10/3, then there are 4 roots in arithmetic progression
    intro ha 
    rw [ha] at *
    use -Real.sqrt 3, -Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 
    constructor 
    · -- Show x ≠ y 
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    constructor 
    · -- Show y ≠ z 
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    constructor 
    · -- Show z ≠ w 
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    constructor 
    · -- Show that x is a root 
      have h1 : (-Real.sqrt 3) ^4 - (10 / 3) * (-Real.sqrt 3) ^2 + 1 = 0 := by 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      nlinarith 
    constructor 
    · -- Show that y is a root 
      have h2 : (-Real.sqrt 3 / 3) ^4 - (10 / 3) * (-Real.sqrt 3 / 3) ^2 + 1 = 0 := by 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      nlinarith 
    constructor 
    · -- Show that z is a root 
      have h3 : (Real.sqrt 3 / 3) ^4 - (10 / 3) * (Real.sqrt 3 / 3) ^2 + 1 = 0 := by 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      nlinarith 
    constructor 
    · -- Show that w is a root 
      have h4 : (Real.sqrt 3) ^4 - (10 / 3) * (Real.sqrt 3) ^2 + 1 = 0 := by 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      nlinarith 
    · -- Show the existence of a common difference 
      use (Real.sqrt 3 / 3 - (-Real.sqrt 3)) / 2 
      constructor 
      · -- Show y = x + d 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      constructor 
      · -- Show z = y + d 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      · -- Show w = z + d 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]