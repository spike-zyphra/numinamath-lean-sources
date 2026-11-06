import Mathlib

open Real

lemma lemma_1 (n : ℝ) (hn : 0 < n) :
    arcsin (1 / sqrt (n ^ 2 + 1)) = arctan (1 / n) := by
  have h12 : -1 < (1 / sqrt (n ^ 2 + 1) : ℝ) := by
    have h6 : sqrt (n ^ 2 + 1) > 0 := by positivity
    have h10 : (1 / sqrt (n ^ 2 + 1) : ℝ) > 0 := by
      apply div_pos
      .
        norm_num
      all_goals
      positivity
    nlinarith
  have h13 : (1 / sqrt (n ^ 2 + 1) : ℝ) < 1 := by
    have h14 : sqrt (n ^ 2 + 1) > 1 := by
      have h15 : sqrt (n ^ 2 + 1) > sqrt (1 : ℝ) := by
        apply Real.sqrt_lt_sqrt
        all_goals
          nlinarith
      have h16 : sqrt (1 : ℝ) = (1 : ℝ) := by
        rw [Real.sqrt_one]
      nlinarith [h15, h16]
    have h14_pos : sqrt (n ^ 2 + 1) > 0 := by positivity
    have h101 : (1 / sqrt (n ^ 2 + 1) : ℝ) < (1 : ℝ) := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  have h1 : (1 / sqrt (n ^ 2 + 1) : ℝ) ∈ Set.Ioo (-1) 1 := by
    constructor
    .
      linarith [h12]
    .
      linarith [h13]
  have h2 : arcsin (1 / sqrt (n ^ 2 + 1)) = arctan ((1 / sqrt (n ^ 2 + 1)) / Real.sqrt (1 - (1 / sqrt (n ^ 2 + 1)) ^ 2)) := by
    rw [Real.arcsin_eq_arctan]
    exact h1
  have h3 : Real.sqrt (1 - (1 / sqrt (n ^ 2 + 1)) ^ 2) = (n / sqrt (n ^ 2 + 1)) := by
    have h36 : Real.sqrt (1 - (1 / sqrt (n ^ 2 + 1)) ^ 2) = Real.sqrt (n^2 / (n^2 + 1 : ℝ)) := by
      have h40 : (1 - (1 / sqrt (n ^ 2 + 1)) ^ 2 : ℝ) = (n^2 / (n^2 + 1 : ℝ)) := by
        have h44 : sqrt (n^2 + 1 : ℝ) ^ 2 = (n^2 + 1 : ℝ) := by
          rw [Real.sq_sqrt]
          positivity
        field_simp [h44]
        <;> nlinarith
      rw [h40]
    rw [h36]
    have h37 : Real.sqrt (n^2 / (n^2 + 1 : ℝ)) = Real.sqrt (n^2 : ℝ) / Real.sqrt (n^2 + 1 : ℝ) := by
      rw [Real.sqrt_div (by positivity)]
    rw [h37]
    have h38 : Real.sqrt (n^2 : ℝ) = (n : ℝ) := by
      rw [Real.sqrt_sq (show 0 ≤ (n : ℝ) by linarith)]
    rw [h38]
  have h4 : (1 / sqrt (n ^ 2 + 1)) / Real.sqrt (1 - (1 / sqrt (n ^ 2 + 1)) ^ 2) = (1 / n) := by
    rw [h3]
    have h7 : sqrt (n ^ 2 + 1) > 0 := by positivity
    have h8 : (n : ℝ) > 0 := by linarith
    field_simp
  rw [h2, h4]


theorem algebra_111088 : arcsin (1 / sqrt 10) + arcsin (1 / sqrt 26) +
    arcsin (1 / sqrt 50) + arcsin (1 / sqrt 65) = π / 4 := by
  have h1 : arcsin (1 / sqrt 10) = arctan (1 / 3) := by
    have h2 : arcsin (1 / sqrt 10) = arctan (1 / 3) := by
      have h3 : arcsin (1 / sqrt 10) = arctan (1 / (3 : ℝ)) := by
        rw [show arcsin (1 / sqrt 10) = arcsin (1 / sqrt ((3 : ℝ) ^ 2 + 1)) by
          ring_nf
        ]
        rw [lemma_1 (3 : ℝ) (by norm_num)]
      norm_num at h3 ⊢
      all_goals linarith
    exact h2

  have h2 : arcsin (1 / sqrt 26) = arctan (1 / 5) := by
    have h3 : arcsin (1 / sqrt 26) = arctan (1 / 5) := by
      have h4 : arcsin (1 / sqrt 26) = arctan (1 / (5 : ℝ)) := by
        rw [show arcsin (1 / sqrt 26) = arcsin (1 / sqrt ((5 : ℝ) ^ 2 + 1)) by
          ring_nf
        ]
        rw [lemma_1 (5 : ℝ) (by norm_num)]
      norm_num at h4 ⊢
      all_goals linarith
    exact h3

  have h3 : arcsin (1 / sqrt 50) = arctan (1 / 7) := by
    have h4 : arcsin (1 / sqrt 50) = arctan (1 / 7) := by
      have h5 : arcsin (1 / sqrt 50) = arctan (1 / (7 : ℝ)) := by
        rw [show arcsin (1 / sqrt 50) = arcsin (1 / sqrt ((7 : ℝ) ^ 2 + 1)) by
          ring_nf
        ]
        rw [lemma_1 (7 : ℝ) (by norm_num)]
      norm_num at h5 ⊢
      all_goals linarith
    exact h4

  have h4 : arcsin (1 / sqrt 65) = arctan (1 / 8) := by
    have h5 : arcsin (1 / sqrt 65) = arctan (1 / 8) := by
      have h6 : arcsin (1 / sqrt 65) = arctan (1 / (8 : ℝ)) := by
        rw [show arcsin (1 / sqrt 65) = arcsin (1 / sqrt ((8 : ℝ) ^ 2 + 1)) by
          ring_nf
        ]
        rw [lemma_1 (8 : ℝ) (by norm_num)]
      norm_num at h6 ⊢
      all_goals linarith
    exact h5

  rw [h1, h2, h3, h4]

  have h5 : arctan (1 / 3) + arctan (1 / 5) = arctan (4 / 7) := by
    rw [arctan_add]
    norm_num
    all_goals norm_num

  have h6 : arctan (4 / 7) + arctan (1 / 7) = arctan (7 / 9) := by
    rw [arctan_add]
    norm_num
    all_goals norm_num

  have h7 : arctan (7 / 9) + arctan (1 / 8) = Real.pi / 4 := by
    have h8 : arctan (7 / 9) + arctan (1 / 8) = arctan (1 : ℝ) := by
      rw [arctan_add]
      norm_num
      all_goals norm_num
    rw [h8]
    have h9 : arctan (1 : ℝ) = Real.pi / 4 := by
      rw [arctan_one]
    rw [h9]

  linarith [h5, h6, h7]