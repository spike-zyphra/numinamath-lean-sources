import Mathlib

theorem algebra_194152 (x : ℝ) :
    x^2 - ⌊x⌋ = 1 ↔ x = Real.sqrt 2 := by
  constructor
  · -- Assume x^2 - ⌊x⌋ = 1, prove x = Real.sqrt 2
    intro h
    have h1 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
    have h2 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have h3 : x^2 = (⌊x⌋ + 1 : ℝ) := by
      have h4 : x^2 - (⌊x⌋ : ℝ) = 1 := by
        exact_mod_cast h
      nlinarith
    have h6 : ⌊x⌋ ≤ 1 := by
      by_contra h7
      push_neg at h7
      have h7' : ⌊x⌋ ≥ 2 := by omega
      have h8 : (⌊x⌋ : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h7'
      nlinarith [sq_nonneg (x - (2 : ℝ)), sq_nonneg (x + (2 : ℝ)), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    have h7 : ⌊x⌋ ≥ 1 := by
      by_contra h8
      push_neg at h8
      have h8' : ⌊x⌋ ≤ 0 := by omega
      have h9 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h8'
      by_cases h11 : ⌊x⌋ = 0
      · -- Assume floor x = 0
        have h12 : (⌊x⌋ : ℝ) = (0 : ℝ) := by
          exact_mod_cast h11
        have h13 : x^2 = (1 : ℝ) := by
          nlinarith [h3, h12
          ]
        have h14 : x = (1 : ℝ) ∨ x = (-1 : ℝ) := by
          have h15 : x^2 = (1 : ℝ) := h13
          have : x^2 - (1 : ℝ) = 0 := by nlinarith
          have : (x - (1 : ℝ)) * (x + (1 : ℝ)) = 0 := by nlinarith
          cases (mul_eq_zero.1 this) with
          | inl h17 => 
            left
            linarith
          | inr h18 => 
            right
            linarith
        cases h14 with
        | inl h15 => 
          -- Check for x = 1
          nlinarith [h15, h1, h2, h12]
        | inr h16 => 
          -- Check for x = -1
          nlinarith [h16, h1, h2, h12
          ]
      · -- Assume floor x < 0
        have h12 : ⌊x⌋ < (0 : Int) := by
          omega
        have h13 : ⌊x⌋ ≤ (-1 : Int) := by
          omega
        have h14 : (⌊x⌋ : ℝ) ≤ (-1 : ℝ) := by
          exact_mod_cast h13
        by_cases h22 : ⌊x⌋ = (-1 : Int)
        · -- Case floor x = -1
          have h23 : (⌊x⌋ : ℝ) = (-1 : ℝ) := by
            exact_mod_cast h22
          have h24 : x^2 = (0 : ℝ) := by
            nlinarith [h3, h23
            ]
          have h25 : x = (0 : ℝ) := by
            nlinarith
          have h26 : (⌊x⌋ : ℝ) = (-1 : ℝ) := h23
          -- Check for x = 0
          nlinarith [h25, h1, h2, h26]
        · -- Assume floor x < -1
          have h27 : ⌊x⌋ ≤ (-2 : Int) := by
            omega
          have h28 : (⌊x⌋ : ℝ) ≤ (-2 : ℝ) := by
            exact_mod_cast h27
          have h29 : x^2 ≤ (-1 : ℝ) := by
            nlinarith [h3, h28]
          have h30 : x^2 ≥ (0 : ℝ) := by
            nlinarith [sq_nonneg x
            ]
          nlinarith
    have h8 : ⌊x⌋ = 1 := by
      omega
    have h9 : (⌊x⌋ : ℝ) = (1 : ℝ) := by
      exact_mod_cast h8
    have h10 : x^2 = (2 : ℝ) := by
      nlinarith [h3, h9
      ]
    have h11 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
      apply eq_or_eq_neg_of_sq_eq_sq
      norm_num
      linarith
    rcases h11 with (h12 | h13)
    · linarith
    · -- Show that x = -sqrt 2 is invalid
      have h14 : x < (0 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Assume x = Real.sqrt 2, prove x^2 - ⌊x⌋ = 1
    intro h
    rw [h]
    have h1 : ⌊Real.sqrt 2⌋ = 1 := by
      have h2 : 1 < Real.sqrt 2 := by
        rw [Real.lt_sqrt]
        all_goals norm_num
      have h3 : Real.sqrt 2 < (2 : ℝ) := by
        rw [Real.sqrt_lt]
        all_goals norm_num
      rw [Int.floor_eq_iff
      ]
      constructor <;> (try norm_num) <;> nlinarith
    rw [h1
    ]
    norm_num
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]