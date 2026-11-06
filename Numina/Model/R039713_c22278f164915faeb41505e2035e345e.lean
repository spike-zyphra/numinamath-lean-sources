import Mathlib

open Real Set

theorem algebra_160062 (a : ℝ) (ha : a > 0) (x y : ℝ) :
    (∃ θ ∈ Set.Icc 0 π, (x, y) = (a * (θ - sin θ), a * (1 - cos θ))) ↔ (x = a * arccos (1 - y / a) - sqrt (2 * y * a - y ^ 2) ∧ 0 ≤ y ∧ y ≤ 2 * a) := by
  constructor
  · -- Prove the forward direction.
    rintro ⟨θ, hθ, h_eq⟩
    rcases hθ with ⟨h1, h2⟩
    have h3 : x = a * (θ - sin θ) := by
      simp [Prod.ext_iff] at h_eq
      linarith
    have h4 : y = a * (1 - cos θ) := by
      simp [Prod.ext_iff] at h_eq
      linarith
    have h5 : 0 ≤ y := by
      have h6 : 0 ≤ 1 - cos θ := by
        have h7 : -1 ≤ cos θ ∧ cos θ ≤ 1 := by
          constructor
          · exact neg_one_le_cos θ
          · exact cos_le_one θ
        linarith
      have h8 : 0 ≤ a * (1 - cos θ) := by
        apply mul_nonneg
        linarith
        linarith
      linarith [show y = a * (1 - cos θ) by linarith]
    have h9 : y ≤ 2 * a := by
      have h10 : 1 - cos θ ≤ 2 := by
        have h7 : -1 ≤ cos θ ∧ cos θ ≤ 1 := by
          constructor
          · exact neg_one_le_cos θ
          · exact cos_le_one θ
        linarith
      have h11 : a * (1 - cos θ) ≤ 2 * a := by
        nlinarith
      linarith [show y = a * (1 - cos θ) by linarith]
    have h10 : x = a * arccos (1 - y / a) - sqrt (2 * y * a - y ^ 2) := by
      have h18 : 1 - y / a = Real.cos θ := by
        have h19 : y = a * (1 - cos θ) := by
          simp [Prod.ext_iff] at h_eq
          linarith
        field_simp [show a ≠ 0 by linarith]
        nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
      have h20 : Real.arccos (1 - y / a) = θ := by
        rw [show 1 - y / a = Real.cos θ by linarith [h18]]
        have h21 : Real.arccos (Real.cos θ) = θ := by
          rw [Real.arccos_cos]
          all_goals
            linarith [Real.pi_pos]
        linarith
      have h23 : Real.sqrt (2 * y * a - y ^ 2) = a * Real.sin θ := by
        have h24 : 2 * y * a - y ^ 2 = (a ^ 2) * (Real.sin θ) ^ 2 := by
          have h19 : y = a * (1 - cos θ) := by
            simp [Prod.ext_iff] at h_eq
            linarith
          rw [h19]
          have h26 : 2 * (a * (1 - cos θ)) * a - (a * (1 - cos θ)) ^ 2 = a ^ 2 * (1 - cos θ ^ 2) := by
            ring_nf
          rw [h26]
          have h27 : 1 - cos θ ^ 2 = (Real.sin θ) ^ 2 := by
            have h28 : (Real.sin θ) ^ 2 + (Real.cos θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
            have h29 : 1 - (Real.cos θ) ^ 2 = (Real.sin θ) ^ 2 := by linarith
            linarith
          rw [h27]
        have h22 : Real.sin θ ≥ 0 := by
          apply Real.sin_nonneg_of_nonneg_of_le_pi
          all_goals
            linarith
        have h23 : Real.sqrt (2 * y * a - y ^ 2) = a * Real.sin θ := by
          rw [h24]
          have h24 : Real.sqrt ((a ^ 2) * (Real.sin θ) ^ 2) = Real.sqrt (a^2) * Real.sqrt ((Real.sin θ) ^ 2) := by
            rw [Real.sqrt_mul (by positivity)]
          rw [h24]
          have h25 : Real.sqrt (a ^ 2) = a := by
            rw [Real.sqrt_sq (show 0 ≤ a by linarith)]
          have h26 : Real.sqrt ((Real.sin θ) ^ 2) = Real.sin θ := by
            rw [Real.sqrt_sq (show 0 ≤ Real.sin θ by linarith [h22])]
          rw [h25, h26]
          all_goals
            nlinarith
        linarith
      have h23' : x = a * θ - a * Real.sin θ := by
        have h3' : x = a * (θ - Real.sin θ) := by
          linarith
        linarith
      have h23'' : a * θ = a * Real.arccos (1 - y / a) := by
        rw [show θ = Real.arccos (1 - y / a) by linarith [h20]]
      linarith [h23', h23'', h23]
    constructor
    · linarith
    constructor
    · linarith
    · linarith
  · -- Prove the reverse direction.
    rintro ⟨hx, hy1, hy2⟩
    have h2 : 0 ≤ y := hy1
    have h3 : y ≤ 2 * a := hy2
    have hx_eq : x = a * arccos (1 - y / a) - sqrt (2 * y * a - y ^ 2) := hx
    have h5 : 1 - y / a ≥ -1 := by
      have h6 : y ≤ 2 * a := by linarith
      have h7 : y / a ≤ 2 := by
        apply (div_le_iff₀ (by linarith)).mpr
        nlinarith
      linarith
    have h6 : 1 - y / a ≤ 1 := by
      have h7 : y ≥ 0 := by linarith
      have h8 : y / a ≥ 0 := by
        apply div_nonneg
        all_goals linarith
      linarith
    set θ := Real.arccos (1 - y / a) with hθ
    use θ
    constructor
    · -- Show θ ∈ [0, π]
      have h7 : θ ∈ Set.Icc 0 Real.pi := by
        have h8 : 0 ≤ θ := Real.arccos_nonneg (1 - y / a)
        have h9 : θ ≤ Real.pi := Real.arccos_le_pi (1 - y / a)
        exact ⟨by linarith, by linarith⟩
      exact h7
    · -- Show (x, y) = (a * (θ - sin θ), a * (1 - cos θ))
      have h10 : Real.cos θ = 1 - y / a := by
        rw [show θ = Real.arccos (1 - y / a) by linarith [hθ]]
        rw [Real.cos_arccos]
        all_goals
          have h4 : -1 ≤ 1 - y / a := by
            linarith
          have h5 : 1 - y / a ≤ 1 := by
            linarith
          all_goals
            try nlinarith
      have h11 : Real.sin θ ≥ 0 := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · -- Show 0 ≤ θ
          have h9 : 0 ≤ θ := Real.arccos_nonneg (1 - y / a)
          linarith
        · -- Show θ ≤ Real.pi
          have h10 : θ ≤ Real.pi := Real.arccos_le_pi (1 - y / a)
          linarith
      have h101 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
        have h16 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
        linarith
      have h112 : Real.sin θ ^ 2 = (2 * y * a - y ^ 2) / a ^ 2 := by
        have h101' : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := h101
        rw [h101']
        rw [show Real.cos θ = 1 - y / a by linarith [h10]]
        field_simp
        nlinarith
      have h104 : Real.sin θ = Real.sqrt (2 * y * a - y ^ 2) / a := by
        have h11' : Real.sin θ ≥ 0 := h11
        have h104' : Real.sin θ ^ 2 = (2 * y * a - y ^ 2) / a ^ 2 := h112
        have h126 : Real.sin θ = Real.sqrt ((2 * y * a - y ^ 2) / a ^ 2) := by
          have h153 : Real.sin θ ≥ 0 := h11
          have h165 : Real.sin θ = Real.sqrt (Real.sin θ ^ 2) := by
            rw [Real.sqrt_sq_eq_abs]
            rw [abs_of_nonneg h11]
          rw [h165, h104']
        have h45 : Real.sqrt ((2 * y * a - y ^ 2) / a ^ 2) = Real.sqrt (2 * y * a - y ^ 2) / a := by
          have h17 : 0 ≤ a := by linarith
          have h42 : Real.sqrt ((2 * y * a - y ^ 2) / a ^ 2) = Real.sqrt (2 * y * a - y ^ 2) / a := by
            have h13 : Real.sqrt ((2 * y * a - y ^ 2) / a^2) = Real.sqrt (2 * y * a - y ^ 2) / Real.sqrt (a ^ 2) := by
              rw [Real.sqrt_div (by
                nlinarith
              )]
            rw [h13]
            have h14 : Real.sqrt (a ^ 2) = a := Real.sqrt_sq (by linarith)
            rw [h14]
          linarith
        rw [h45] at h126
        linarith
      have h14 : a * (θ - Real.sin θ) = x := by
        have h23 : a * (θ - Real.sin θ) = a * θ - a * Real.sin θ := by ring
        rw [h23]
        have h23 : a * θ = a * arccos (1 - y / a) := by
          rw [show θ = Real.arccos (1 - y / a) by linarith [hθ]]
        have h24 : a * Real.sin θ = Real.sqrt (2 * y * a - y ^ 2) := by
          rw [h104]
          field_simp
        rw [h23, h24]
        nlinarith [hx_eq]
      have h82 : a * (1 - Real.cos θ) = y := by
        have h108 : Real.cos θ = 1 - y / a := h10
        have h36 : a * (1 - Real.cos θ) = y := by
          rw [h108]
          field_simp
          <;> nlinarith
        linarith
      simp [Prod.ext_iff]
      constructor
      · linarith
      · linarith