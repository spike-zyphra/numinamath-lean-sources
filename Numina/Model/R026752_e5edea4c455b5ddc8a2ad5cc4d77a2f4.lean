import Mathlib


theorem algebra_152025 (a b c d e : ℝ) (hf : ∀ x ∈ Set.Icc (-1) 1, a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e ∈ Set.Icc (-1) 1) :
    |c| ≤ 8 := by

  have h1 := hf 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h2 := hf (-1) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h3 := hf (1 / 2 : ℝ) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h4 := hf (-1 / 2 : ℝ) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h5 := hf (0 : ℝ) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h6 := hf (Real.sqrt 2 / 2) (by
    constructor
    · -- Show sqrt(2)/2 ≥ -1
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    · -- Show sqrt(2)/2 ≤ 1
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  )
  have h7 := hf (-Real.sqrt 2 / 2) (by
    constructor
    · -- Show -sqrt(2)/2 ≥ -1
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    · -- Show -sqrt(2)/2 ≤ 1
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  )

  rcases h1 with ⟨h11, h12⟩
  rcases h2 with  ⟨h21, h22⟩
  rcases h3 with  ⟨h31, h32⟩
  rcases h4 with  ⟨h41, h42⟩
  rcases h5 with  ⟨h51, h52⟩
  rcases h6 with  ⟨h61, h62⟩
  rcases h7 with  ⟨h71, h72⟩

  simp at h11 h12 h21 h22 h31 h32 h41 h42 h51 h52 h61 h62 h71 h72

  have h83 : -4 ≤ a * (Real.sqrt 2 / 2) ^ 4 + b * (Real.sqrt 2 / 2) ^ 3 + c * (Real.sqrt 2 / 2) ^ 2 + d * (Real.sqrt 2 / 2) + e + (a * (-Real.sqrt 2 / 2) ^ 4 + b * (-Real.sqrt 2 / 2) ^ 3 + c * (-Real.sqrt 2 / 2) ^ 2 + d * (-Real.sqrt 2 / 2) + e) := by
    nlinarith

  have h84 : a * (Real.sqrt 2 / 2) ^ 4 + b * (Real.sqrt 2 / 2) ^ 3 + c * (Real.sqrt 2 / 2) ^ 2 + d * (Real.sqrt 2 / 2) + e + (a * (-Real.sqrt 2 / 2) ^ 4 + b * (-Real.sqrt 2 / 2) ^ 3 + c * (-Real.sqrt 2 / 2) ^ 2 + d * (-Real.sqrt 2 / 2) + e) = a/2 + c + 2 * e := by
    have h93 : 0 < (Real.sqrt 2 : ℝ) := by
      positivity
    have h94 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h95 : (Real.sqrt 2 / 2 : ℝ) ^ 4 = 1 / 4 := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 4 = ((Real.sqrt 2 / 2) ^ 2) ^ 2 := by ring
        _ = (1 / 2) ^ 2 := by rw [h94]
        _ = (1 / 4 : ℝ) := by norm_num
    have h98 : b * (Real.sqrt 2 / 2 : ℝ) ^ 3 + b * (-Real.sqrt 2 / 2 : ℝ) ^ 3 = 0 := by
      have h96 : (-Real.sqrt 2 / 2 : ℝ) ^ 3 = - (Real.sqrt 2 / 2 : ℝ) ^ 3 := by
        ring
      nlinarith [h96]
    have h99 : d * (Real.sqrt 2 / 2 : ℝ) + d * (-Real.sqrt 2 / 2 : ℝ) = 0 := by
      ring
    nlinarith [h94, h95, h98, h99]

  have h106 : -8 ≤ c := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]

  have h107 : c ≤ 8 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]

  apply abs_le.mpr
  constructor
  · linarith [h106]
  · linarith [h107]