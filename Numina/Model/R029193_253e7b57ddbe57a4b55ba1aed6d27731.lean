import Mathlib

theorem algebra_260527 {a b c : ℝ} (F G : ℝ → ℝ)
    (hF : ∀ x, F x = a * x ^ 2 + b * x + c)
    (hG : ∀ x, G x = c * x ^ 2 + b * x + a)
    (hF0 : |F 0| ≤ 1) (hF1 : |F 1| ≤ 1) (hFm1 : |F (-1)| ≤ 1) :
    (∀ x, |x| ≤ 1 → |F x| ≤ 5 / 4) ∧ (∀ x, |x| ≤ 1 → |G x| ≤ 2) := by

  have h11 : F 0 = c := by 
    simp [hF]

  have h12 : F 1 = a + b + c := by
    simp [hF]
    <;> ring

  have h13 : F (-1) = a - b + c := by 
    simp [hF]
    <;> ring

  have h14 : -1 ≤ c := by 
    have : |F 0| ≤ 1 := hF0
    rw [show F 0 = c by linarith [h11]] at this 
    cases' abs_le.mp this with h15 h16 
    linarith

  have h15 : c ≤ 1 := by 
    have : |F 0| ≤ 1 := hF0 
    rw [show F 0 = c by linarith [h11]] at this 
    cases' abs_le.mp this with h16 h17 
    linarith

  have h18 : -1 ≤ a + b + c := by
    have : |F 1| ≤ 1 := hF1 
    rw [show F 1 = a + b + c by linarith [h12]] at this 
    cases' abs_le.mp this with h19 h20 
    linarith

  have h19 : a + b + c ≤ 1 := by 
    have : |F 1| ≤ 1 := hF1 
    rw [show F 1 = a + b + c by linarith [h12]] at this 
    cases' abs_le.mp this with h19 h20 
    linarith

  have h20 : -1 ≤ a - b + c := by 
    have : |F (-1)| ≤ 1 := hFm1 
    rw [show F (-1) = a - b + c by linarith [h13]] at this 
    cases' abs_le.mp this with h21 h22 
    linarith

  have h21 : a - b + c ≤ 1 := by 
    have : |F (-1)| ≤ 1 := hFm1 
    rw [show F (-1) = a - b + c by linarith [h13]] at this 
    cases' abs_le.mp this with h21 h22 
    linarith

  constructor
  · -- Prove: ∀ x, |x| ≤ 1 → |F x| ≤ 5 / 4
    intro x hx
    have h22 : -1 ≤ x := by 
      cases' abs_le.mp hx with h23 h24 
      linarith

    have h23 : x ≤ 1 := by 
      cases' abs_le.mp hx with h24 h25
      linarith

    have h24 : x ^ 2 ≤ 1 := by 
      nlinarith

    have h25 : -5 / 4 ≤ a * x ^ 2 + b * x + c := by 
      by_cases h26 : x ≥ 0 
      · -- Case where x ≥ 0 
        have h27 : x ≤ 1 := by linarith 
        nlinarith [sq_nonneg (x - 1/2), sq_nonneg (x + 1/2), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
          mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ 1 - x by nlinarith)
        ]
      · -- Case where x < 0 
        have h28 : x ≥ -1 := by linarith 
        nlinarith [sq_nonneg (x + 1/2), sq_nonneg (x - 1/2), 
          sq_nonneg (a + b), sq_nonneg (b - c), sq_nonneg (a - c), 
          mul_nonneg (show (0 : ℝ) ≤ -x by nlinarith) (show (0 : ℝ) ≤ 1 + x by nlinarith)
        ]

    have h26 : a * x ^ 2 + b * x + c ≤ 5 / 4 := by 
      by_cases h27 : x ≥ 0 
      · -- Case where x ≥ 0 
        have h28 : x ≤ 1 := by linarith 
        nlinarith [sq_nonneg (x - 1/2), sq_nonneg (x + 1/2), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
          mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ 1 - x by nlinarith)
        ]
      · -- Case where x < 0 
        have h29 : x ≥ -1 := by linarith 
        nlinarith [sq_nonneg (x + 1/2), sq_nonneg (x - 1/2), 
          sq_nonneg (a + b), sq_nonneg (b - c), sq_nonneg (a - c), 
          mul_nonneg (show (0 : ℝ) ≤ -x by nlinarith) (show (0 : ℝ) ≤ 1 + x by nlinarith)
        ]

    have h28 : F x = a * x ^ 2 + b * x + c := by 
      apply hF 
    rw [h28]
    apply abs_le.mpr 
    constructor <;> linarith [h25, h26]

  · -- Prove: ∀ x, |x| ≤ 1 → |G x| ≤ 2
    intro x hx 
    have h22 : -1 ≤ x := by 
      cases' abs_le.mp hx with h23 h24 
      linarith 
    have h23 : x ≤ 1 := by 
      cases' abs_le.mp hx with h24 h25 
      linarith 
    have h24 : x ^ 2 ≤ 1 := by 
      nlinarith

    have h25' : -2 ≤ c * x ^ 2 + b * x + a := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), 
        mul_nonneg (show (0 : ℝ) ≤ 1 - x by nlinarith) (show (0 : ℝ) ≤ x + 1 by nlinarith) 
      ]

    have h26' : c * x ^ 2 + b * x + a ≤ 2 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), 
        mul_nonneg (show (0 : ℝ) ≤ 1 - x by nlinarith) (show (0 : ℝ) ≤ x + 1 by nlinarith) 
      ]

    have h29 : G x = c * x ^ 2 + b * x + a := by 
      apply hG 
    rw [h29] 
    apply abs_le.mpr 
    constructor <;> linarith [h25', h26']