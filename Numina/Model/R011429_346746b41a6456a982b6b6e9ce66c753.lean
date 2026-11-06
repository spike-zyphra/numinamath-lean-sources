import Mathlib

theorem algebra_258450 (d splitPos meetPos: ℝ) (h₀ : d > 0 ∧ meetPos > 0) (hsplit: splitPos = d/5) (v_ab v_a v_b vf : ℝ)
(hpos: v_ab > 0 ∧ vf > 0)
(hva: v_a = v_ab * 5 / 4) (hvb: v_b = v_ab * 3 / 4) (hvf: vf = 48)
(hmeet: splitPos/v_ab + splitPos/v_a + meetPos/v_a = splitPos/v_ab + (meetPos - splitPos)/v_b)
(hArrival: splitPos/v_ab + splitPos/v_a + meetPos/v_a + (d - meetPos)/vf = d/v_ab + 1/6)
  : d=40 := by
    have ha1 : d > 0 := h₀.1
    have hm1 : meetPos > 0 := h₀.2
    have hv1 : v_ab > 0 := hpos.1
    have hv2 : vf > 0 := hpos.2
    have eq1 : splitPos + meetPos = (meetPos - splitPos) * (v_a / v_b) := by 
      have h1 : splitPos / v_a + meetPos / v_a = (meetPos - splitPos) / v_b := by
        have eq1 : splitPos / v_ab + splitPos / v_a + meetPos / v_a = splitPos / v_ab + (meetPos - splitPos) / v_b := hmeet 
        linarith 
      have h_eq1 : (splitPos + meetPos) / v_a = (meetPos - splitPos) / v_b := by
        have h2 : (splitPos + meetPos) / v_a = splitPos / v_a + meetPos / v_a := by 
          field_simp [(show v_a ≠ 0 by 
            by_contra h
            have : v_a = 0 := by nlinarith 
            rw [this] at hva 
            nlinarith 
          )] 
        rw [h2] 
        all_goals linarith [h1] 
      have h_eq2 : splitPos + meetPos = (meetPos - splitPos) * (v_a / v_b) := by 
        have h3 : (splitPos + meetPos) / v_a = (meetPos - splitPos) / v_b := h_eq1 
        have h4 : v_a ≠ 0 := by 
          by_contra h 
          have : v_a = 0 := by nlinarith 
          rw [this] at hva 
          nlinarith 
        have h5 : v_b ≠ 0 := by 
          by_contra h 
          have : v_b = 0 := by nlinarith 
          rw [this] at hvb 
          nlinarith 
        field_simp [h4, h5] at h3 ⊢ 
        <;> nlinarith 
      linarith 
    have eq2 : meetPos = 4 * splitPos := by 
      rw [hva, hvb] at eq1 
      have : v_ab > 0 := hv1 
      field_simp [(show v_ab ≠ 0 by linarith)] at eq1 ⊢ 
      ring_nf at eq1 
      nlinarith [ha1, hm1] 
    have eq3 : meetPos = 4 * d / 5 := by 
      rw [hsplit] at eq2 
      linarith 
    have h1 : splitPos / v_ab + splitPos / v_a + meetPos / v_a + (d - meetPos) / vf = d / v_ab + 1/6 := by linarith [hArrival]
    have h2 : (d / 5) / v_ab + (d / 5) / v_a + (4 * d / 5) / v_a + (d - 4 * d / 5) / vf = d / v_ab + 1/6 := by
      rw [hsplit] at h1 
      rw [eq3] at h1 
      linarith 
    have h3 : (d / (5 * v_ab) ) + (d / v_a) + (d / (5 * vf) ) = d / v_ab + 1 / 6 := by 
      have eq4 : (d / 5) / v_ab = d / (5 * v_ab) := by 
        field_simp [(show v_ab ≠ 0 by linarith)]
        <;> ring 
      have eq5 : (d / 5) / v_a = d / (5 * v_a) := by 
        field_simp [(show v_a ≠ 0 by 
          by_contra h 
          have : v_a = 0 := by nlinarith 
          rw [this] at hva 
          nlinarith 
        )] 
      have eq6 : (4 * d / 5) / v_a = 4 * d / (5 * v_a) := by 
        field_simp [(show v_a ≠ 0 by 
          by_contra h 
          have : v_a = 0 := by nlinarith 
          rw [this] at hva 
          nlinarith 
        )] 
      have eq7 : (d - 4 * d / 5) / vf = d / (5 * vf) := by 
        have eq8 : d - 4 * d / 5 = d / 5 := by 
          linarith 
        rw [eq8] 
        all_goals 
        field_simp [(show vf ≠ 0 by linarith )] 
      rw [eq4, eq5, eq6, eq7] at h2 
      have h3 : d / (5 * v_a) + 4 * d / (5 * v_a) = d / v_a := by 
        field_simp [(show v_a ≠ 0 by 
          by_contra h 
          have : v_a = 0 := by nlinarith 
          rw [this] at hva 
          nlinarith 
        ), (show v_ab ≠ 0 by linarith)]
        <;> ring 
      nlinarith [h3] 
    have h4 : (d / (5 * v_ab) ) + (d / (5 / 4 * v_ab) ) + (d / (5 * vf) ) = d / v_ab + 1 / 6 := by 
      have h5 : v_a = 5 / 4 * v_ab := by 
        linarith [hva] 
      rw [h5] at h3 
      linarith 
    have h5 : (d / (5 * v_ab) ) + (d / (5 / 4 * v_ab) ) + (d / (5 * (48 : ℝ) ) ) = d / v_ab + 1 / 6 := by 
      rw [show vf = (48 : ℝ) by linarith [hvf] ] at h4 
      linarith 
    have h6 : (d / v_ab) + (d / (5 * (48 : ℝ) ) ) = d / v_ab + 1 / 6 := by 
      have eq8 : (d / (5 * v_ab) ) + (d / (5 / 4 * v_ab) ) = d / v_ab := by 
        have h8 : (d / (5 * v_ab) ) + (d / (5 / 4 * v_ab) ) = d / v_ab := by 
          field_simp [(show v_ab ≠ 0 by linarith )] 
          <;> ring 
        linarith [h8] 
      linarith [h5, eq8] 
    have h7 : d / (5 * (48 : ℝ) ) = 1 / 6 := by 
      linarith [h6] 
    have h8 : d = 40 := by 
      field_simp at h7 ⊢ 
      nlinarith 
    linarith [h8]