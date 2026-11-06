import Mathlib

open Real

theorem algebra_211711 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hord : a > b ∧ b > c) (p : ℝ) (hp : p = 4 * (a + b + c)) (S : ℝ)
    (hS : S = 2 * (a * b + b * c + c * a)) (d : ℝ) (hd : d = √(a^2 + b^2 + c^2)) :
    a > (p / 4 + √(d^2 - S / 2)) / 3 ∧ c < (p / 4 - √(d^2 - S / 2)) / 3 := by

  have hp1 : p / 4 = a + b + c := by
    rw [hp]
    linarith
  
  have h1 : d ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by 
    rw [hd]
    rw [Real.sq_sqrt (by positivity)]

  have h2 : S / 2 = a * b + b * c + c * a := by 
    rw [hS]
    linarith

  have h3 : d ^ 2 - S / 2 = (a ^ 2 + b ^ 2 + c ^ 2) - (a * b + b * c + c * a) := by 
    rw [h1, h2]

  have h4 : d ^ 2 - S / 2 ≥ 0 := by
    rw [h3]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      hord.1, hord.2, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc
    ]

  have h9 : a > (p / 4 + Real.sqrt (d ^ 2 - S / 2)) / 3 := by 
    have h5 : 2 * a - b - c > 0 := by
      nlinarith [hord.1, hord.2, ha, hb, hc]

    have h7 : (2 * a - b - c) ^ 2 > d ^ 2 - S / 2 := by 
      rw [h3]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        hord.1, hord.2, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]

    have h8 : Real.sqrt ((2 * a - b - c) ^ 2) > Real.sqrt (d ^ 2 - S / 2) := by
      apply Real.sqrt_lt_sqrt
      nlinarith
      nlinarith

    have h11 : Real.sqrt ((2 * a - b - c) ^ 2) = 2 * a - b - c := by 
      rw [Real.sqrt_sq (show 0 ≤ 2 * a - b - c by linarith)]

    nlinarith [Real.sqrt_nonneg (d ^ 2 - S / 2), hp1, h11, h8]

  have h13 : c < (p / 4 - Real.sqrt (d ^ 2 - S / 2)) / 3 := by 
    have h10 : a + b - 2 * c > 0 := by
      nlinarith [hord.1, hord.2, ha, hb, hc]

    have h11 : (a + b - 2 * c) ^ 2 > d ^ 2 - S / 2 := by
      rw [h3]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
        hord.1, hord.2, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]

    have h12 : Real.sqrt ((a + b - 2 * c) ^ 2) > Real.sqrt (d ^ 2 - S / 2) := by
      apply Real.sqrt_lt_sqrt
      nlinarith
      nlinarith

    have h14 : Real.sqrt ((a + b - 2 * c) ^ 2) = a + b - 2 * c := by 
      rw [Real.sqrt_sq (show 0 ≤ a + b - 2 * c by nlinarith)]

    nlinarith [Real.sqrt_nonneg (d ^ 2 - S / 2), hp1, h14, h12]

  constructor
  · exact h9
  · exact h13