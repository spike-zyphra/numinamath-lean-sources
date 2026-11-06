import Mathlib
open Real Set
open scoped BigOperators

theorem calculus_127218 (f : ℝ → ℝ) (hf : f = λ x => x^3 - 6*x^2 + 9*x)
  (a : ℝ) (h : ∃ x ∈ Ioo (3 - a^2) a, f x = 4 ∧ ∀ y ∈ Ioo (3 - a^2) a, f y ≤ 4) :
  a ∈ Ioc (Real.sqrt 2) 4 := by
  rcases h with ⟨x, hx, hx1, hx2⟩
  rcases mem_Ioo.mp hx with ⟨h1, h2⟩
  have h_eq : f x = 4 := hx1
  have h_eq' : x^3 - 6 * x^2 + 9 * x = 4 := by
    rw [hf] at h_eq
    simpa using h_eq
  have h_eq'' : (x - 1)^2 * (x - 4) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp h_eq'') with h_eq3 h_eq4
  · -- Case $h_eq3$
    have h_eq5 : (x - 1)^2 = 0 := h_eq3
    have h_eq6 : x - 1 = 0 := by
      apply pow_eq_zero
      exact h_eq5
    have h_eq7 : x = 1 := by linarith
    have h3 : 3 - a^2 < 1 := by
      rw [h_eq7] at h1
      nlinarith
    have h4 : 1 < a := by
      rw [h_eq7] at h2
      nlinarith
    have h5 : a > Real.sqrt 2 := by
      have ha1 : a ^ 2 > 2 := by
        nlinarith
      have ha7 : a > Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith)]
      exact ha7
    have h8 : a ≤ 4 := by
      by_contra h9
      push_neg at h9
      have h10 : a > 4 := by linarith
      have h90 : ∃ y, y ∈ Ioo (3 - a^2) a ∧ f y > 4 := by
        use (4 + (a - 4) / 2)
        constructor
        · -- Show $4 + (a - 4) / 2 \in (3 - a^2, a)$
          have ha40 : 3 - a^2 < (4 + (a - 4) / 2 : ℝ) := by
            nlinarith [sq_nonneg (a - 4 : ℝ), h10]
          have ha20 : (4 + (a - 4) / 2 : ℝ) < (a : ℝ) := by
            nlinarith [h10]
          exact ⟨ha40, ha20⟩
        · -- Show f ((4 + (a - 4) / 2 : ℝ)) > 4
          have ha12 : (4 + (a - 4) / 2 : ℝ) > (4 : ℝ) := by
            linarith [h10]
          have hx12 : f ((4 + (a - 4) / 2 : ℝ)) = ((4 + (a - 4) / 2 : ℝ)) ^ 3 - 6 * ((4 + (a - 4) / 2 : ℝ)) ^ 2 + 9 * ((4 + (a - 4) / 2 : ℝ)) := by
            rw [hf]
          rw [hx12]
          have h_eq5 : ((4 + (a - 4) / 2 : ℝ)) ^ 3 - 6 * ((4 + (a - 4) / 2 : ℝ)) ^ 2 + 9 * ((4 + (a - 4) / 2 : ℝ)) > (4 : ℝ) := by
            have h_eq40 : ((4 + (a - 4) / 2 : ℝ)) > (4 : ℝ) := by
              nlinarith [h10]
            nlinarith [sq_pos_of_pos (show (0 : ℝ) < ((4 + (a - 4) / 2 : ℝ) - 4 : ℝ) by nlinarith), 
                      sq_nonneg (((4 + (a - 4) / 2 : ℝ)) - 4 : ℝ), 
                      sq_nonneg ((4 + (a - 4) / 2 : ℝ) - 1 : ℝ), 
                      sq_pos_of_pos (show (0 : ℝ) < (4 + (a - 4) / 2 : ℝ) by nlinarith [h10]), 
                      h10
                    ]
          linarith
      rcases h90 with ⟨y, hy7, hy8⟩
      have hx13 : f y ≤ 4 := by
        apply hx2
        exact hy7
      linarith
    have h9 : a ≤ 4 := h8
    exact ⟨by linarith, by linarith⟩
  · -- Case $h_eq4$
    have h_eq8 : x = 4 := by
      linarith
    have h10 : 3 - a^2 < 4 := by
      rw [h_eq8] at h1
      nlinarith
    have h11 : 4 < a := by
      rw [h_eq8] at h2
      nlinarith
    have hx12 : a > 4 := by linarith
    have h8 : a ≤ 4 := by
      by_contra h9
      push_neg at h9
      have h10 : a > 4 := by linarith
      have h90 : ∃ y, y ∈ Ioo (3 - a^2) a ∧ f y > 4 := by
        use (4 + (a - 4) / 2)
        constructor
        · -- Show $4 + (a - 4) / 2 \in (3 - a^2, a)$
          have ha40 : 3 - a^2 < (4 + (a - 4) / 2 : ℝ) := by
            nlinarith [sq_nonneg (a - 4 : ℝ), h10]
          have ha20 : (4 + (a - 4) / 2 : ℝ) < (a : ℝ) := by
            nlinarith [h10]
          exact ⟨ha40, ha20⟩
        · -- Show f ((4 + (a - 4) / 2 : ℝ)) > 4
          have ha12 : (4 + (a - 4) / 2 : ℝ) > (4 : ℝ) := by
            linarith [h10]
          have hx12 : f ((4 + (a - 4) / 2 : ℝ)) = ((4 + (a - 4) / 2 : ℝ)) ^ 3 - 6 * ((4 + (a - 4) / 2 : ℝ)) ^ 2 + 9 * ((4 + (a - 4) / 2 : ℝ)) := by
            rw [hf]
          rw [hx12]
          have h_eq5 : ((4 + (a - 4) / 2 : ℝ)) ^ 3 - 6 * ((4 + (a - 4) / 2 : ℝ)) ^ 2 + 9 * ((4 + (a - 4) / 2 : ℝ)) > (4 : ℝ) := by
            have h_eq40 : ((4 + (a - 4) / 2 : ℝ)) > (4 : ℝ) := by
              nlinarith [h10]
            nlinarith [sq_pos_of_pos (show (0 : ℝ) < ((4 + (a - 4) / 2 : ℝ) - 4 : ℝ) by nlinarith), 
                      sq_nonneg (((4 + (a - 4) / 2 : ℝ)) - 4 : ℝ), 
                      sq_nonneg ((4 + (a - 4) / 2 : ℝ) - 1 : ℝ), 
                      sq_pos_of_pos (show (0 : ℝ) < (4 + (a - 4) / 2 : ℝ) by nlinarith [h10]), 
                      h10
                    ]
          linarith
      rcases h90 with ⟨y, hy7, hy8⟩
      have hx13 : f y ≤ 4 := by
        apply hx2
        exact hy7
      linarith
    linarith