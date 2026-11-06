import Mathlib

lemma lemma_1 {c : ℝ} {r : ℚ} (hr : r^3 - c * r^2 + (c - 3) * r + 1 = 0) :
    ∃ q : ℚ, c = ↑q := by
  have eq1 : (r : ℝ)^3 - c * (r : ℝ)^2 + (c - 3) * (r : ℝ) + 1 = 0 := by
    exact_mod_cast hr
  have eq2 : r ≠ (0 : ℚ) := by
    by_contra h
    have hr0 : r = (0 : ℚ) := by
      exact_mod_cast h
    rw [hr0] at hr
    norm_num at hr
  have eq3 : r ≠ (1 : ℚ) := by
    by_contra h
    have hr1 : r = (1 : ℚ) := by
      exact_mod_cast h
    rw [hr1] at hr
    norm_num at hr
  have eq4 : (r : ℝ) ≠ 0 := by
    exact_mod_cast eq2
  have eq5 : (r : ℝ) ≠ 1 := by
    exact_mod_cast eq3
  have eq6 : (r : ℝ)^2 - (r : ℝ) ≠ 0 := by
    intro h
    have h_eq : (r : ℝ) * ((r : ℝ) - 1) = 0 := by
      linarith
    cases' (mul_eq_zero.mp h_eq) with h_eq1 h_eq2
    ·
      have h_eq3 : (r : ℝ) = 0 := by
        linarith
      have h_eq4 : (r : ℚ) = (0 : ℚ) := by
        exact_mod_cast h_eq3
      contradiction
    ·
      have h_eq3 : (r : ℝ) = 1 := by
        linarith
      have h_eq4 : (r : ℚ) = (1 : ℚ) := by
        exact_mod_cast h_eq3
      contradiction
  have eq7 : c = ((r^3 - 3 * r + 1) / (r^2 - r) : ℝ) := by
    have eq8 : (r : ℝ)^2 - (r : ℝ) ≠ 0 := eq6
    field_simp [eq8]
    nlinarith [eq1]
  use (r^3 - 3 * r + 1) / (r^2 - r)
  rw [eq7]
  norm_num


theorem algebra_48303 {c : ℝ} (h : ∃ x : ℚ, x ^ 3 - c * x ^ 2 + (c - 3) * x + 1 = 0) :
    ∀ x : ℝ, x ^ 3 - c * x ^ 2 + (c - 3) * x + 1 = 0 → ∃ q : ℚ, x = q := by
  intro x hx
  rcases h with ⟨q, hq⟩
  have h1 : ∃ q1 : ℚ, c = ↑q1 := by
    apply lemma_1 (hq)
  rcases h1 with ⟨q1, h2⟩
  have eq1 : c = (q1 : ℝ) := by
    exact_mod_cast h2
  have eq2 : (x : ℝ) ^ 3 - c * (x : ℝ) ^ 2 + (c - 3) * (x : ℝ) + 1 = 0 := by
    linarith
  have eq3 : (x : ℝ) ^ 3 - c * (x : ℝ) ^ 2 + (c - 3) * (x : ℝ) + 1 =
      (x - (q : ℝ)) * (x ^ 2 + ((-q ^ 2 + 3 * q - 1) / (q ^ 2 - q) : ℝ) * x + ((-q + 1) / (q ^ 2 - q) : ℝ)) := by
    have hc : c = (q^3 - 3 * q + 1) / (q^2 - q : ℝ) := by
      have h11 : (q : ℝ)^3 - c * (q : ℝ)^2 + (c - 3) * (q : ℝ) + 1 = 0 := by
        exact_mod_cast hq
      have eq4 : (q : ℝ) ≠ 0 := by
        have eq2 : q ≠ (0 : ℚ) := by
          by_contra h
          have hr0 : q = (0 : ℚ) := by
            exact_mod_cast h
          rw [hr0] at hq
          norm_num at hq
        exact_mod_cast eq2
      have eq5 : (q : ℝ) ≠ 1 := by
        have eq3 : q ≠ (1 : ℚ) := by
          by_contra h
          have hr1 : q = (1 : ℚ) := by
            exact_mod_cast h
          rw [hr1] at hq
          norm_num at hq
        exact_mod_cast eq3
      have eq6 : (q : ℝ)^2 - (q : ℝ) ≠ 0 := by
        intro h
        have h_eq : (q : ℝ) * ((q : ℝ) - 1) = 0 := by
          linarith
        cases' (mul_eq_zero.mp h_eq) with h_eq1 h_eq2
        ·
          have h_eq3 : (q : ℝ) = 0 := by
            linarith
          have h_eq4 : (q : ℚ) = (0 : ℚ) := by
            exact_mod_cast h_eq3
          contradiction
        ·
          have h_eq3 : (q : ℝ) = 1 := by
            linarith
          have h_eq4 : (q : ℚ) = (1 : ℚ) := by
            exact_mod_cast h_eq3
          contradiction
      field_simp [eq6]
      nlinarith [h11]
    rw [hc]
    have eq5 : (q : ℝ) ≠ 0 := by
      have eq2 : q ≠ (0 : ℚ) := by
        by_contra h
        have hr0 : q = (0 : ℚ) := by
          exact_mod_cast h
        rw [hr0] at hq
        norm_num at hq
      exact_mod_cast eq2
    have eq6 : (q : ℝ) ≠ 1 := by
      have eq3 : q ≠ (1 : ℚ) := by
        by_contra h
        have hr1 : q = (1 : ℚ) := by
          exact_mod_cast h
        rw [hr1] at hq
        norm_num at hq
      exact_mod_cast eq3
    field_simp [(show (q : ℝ)^2 - (q : ℝ) ≠ 0 by
      intro h
      have h_eq : (q : ℝ) * ((q : ℝ) - 1) = 0 := by
        linarith
      cases' (mul_eq_zero.mp h_eq) with h_eq1 h_eq2
      ·
        have h_eq3 : (q : ℝ) = 0 := by
          linarith
        have h_eq4 : (q : ℚ) = (0 : ℚ) := by
          exact_mod_cast h_eq3
        contradiction
      ·
        have h_eq3 : (q : ℝ) = 1 := by
          linarith
        have h_eq4 : (q : ℚ) = (1 : ℚ) := by
          exact_mod_cast h_eq3
        contradiction
    )
    ]
    ring
  rw [eq3] at eq2
  cases' (mul_eq_zero.mp eq2) with h3 h4
  ·
    have eq4 : x = (q : ℝ) := by
      linarith
    have eq5 : ∃ q2 : ℚ, x = q2 := by
      refine' ⟨q, by simp [eq4]⟩
    exact eq5
  ·
    have eq4 : (x : ℝ) ^ 2 + ((-q ^ 2 + 3 * q - 1) / (q ^ 2 - q) : ℝ) * x + ((-q + 1) / (q ^ 2 - q) : ℝ) = 0 := by
      linarith
    have eq5 : (q ^ 2 - q : ℝ) ≠ 0 := by
      have eq2 : q ≠ (0 : ℚ) := by
        by_contra h
        have hr0 : q = (0 : ℚ) := by
          exact_mod_cast h
        rw [hr0] at hq
        norm_num at hq
      have eq3 : q ≠ (1 : ℚ) := by
        by_contra h
        have hr1 : q = (1 : ℚ) := by
          exact_mod_cast h
        rw [hr1] at hq
        norm_num at hq
      have eq4 : (q : ℝ) ≠ 0 := by
        exact_mod_cast eq2
      have eq5 : (q : ℝ) ≠ 1 := by
        exact_mod_cast eq3
      intro h
      have h_eq : (q : ℝ) * ((q : ℝ) - 1) = 0 := by
        linarith
      cases' (mul_eq_zero.mp h_eq) with h_eq1 h_eq2
      ·
        have h_eq3 : (q : ℝ) = 0 := by
          linarith
        have h_eq4 : (q : ℚ) = (0 : ℚ) := by
          exact_mod_cast h_eq3
        contradiction
      ·
        have h_eq3 : (q : ℝ) = 1 := by
          linarith
        have h_eq4 : (q : ℚ) = (1 : ℚ) := by
          exact_mod_cast h_eq3
        contradiction
    have eq7 : (q ^ 2 - q : ℝ) * x^2 + (-q^2 + 3 * q - 1) * x + (-q + 1) = 0 := by
      have eq6 : (x : ℝ) ^ 2 + ((-q ^ 2 + 3 * q - 1) / (q ^ 2 - q) : ℝ) * x + ((-q + 1) / (q ^ 2 - q) : ℝ) = 0 := eq4
      have eq8 : (q ^ 2 - q : ℝ) ≠ 0 := eq5
      have eq9 : (q ^ 2 - q : ℝ) * ((x : ℝ) ^ 2 + ((-q ^ 2 + 3 * q - 1) / (q ^ 2 - q) : ℝ) * x + ((-q + 1) / (q ^ 2 - q) : ℝ)) = 0 := by
        rw [eq6]
        norm_num
      have eq10 : (q ^ 2 - q : ℝ) * x^2 + (-q^2 + 3 * q - 1) * x + (-q + 1) = 0 := by
        have eq11 : (q ^ 2 - q : ℝ) * ((x : ℝ) ^ 2 + ((-q ^ 2 + 3 * q - 1) / (q ^ 2 - q) : ℝ) * x + ((-q + 1) / (q ^ 2 - q) : ℝ)) =
            (q ^ 2 - q : ℝ) * x^2 + (-q^2 + 3 * q - 1) * x + (-q + 1) := by
          field_simp [eq8]
          <;> ring
        nlinarith [eq11, eq9]
      linarith
    have eq20 : (x : ℝ) = (q - 1) / (q : ℝ) ∨ (x : ℝ) = -1 / (q - 1 : ℝ) := by
      have h90 : (q ^ 2 - q : ℝ) ≠ 0 := eq5
      have eq91 : (q ^ 2 - q : ℝ) * x^2 + (-q^2 + 3 * q - 1) * x + (-q + 1) = 0 := eq7
      have eq92 : ((x : ℝ) - (q - 1) / (q : ℝ)) * ((x : ℝ) + 1 / (q - 1 : ℝ)) = 0 := by
        have h93 : (q : ℝ) ≠ 0 := by
          have eq2 : q ≠ (0 : ℚ) := by
            by_contra h
            have hr0 : q = (0 : ℚ) := by
              exact_mod_cast h
            rw [hr0] at hq
            norm_num at hq
          exact_mod_cast eq2
        have h94 : (q - 1 : ℝ) ≠ 0 := by
          intro h0
          have h1 : (q : ℝ) = 1 := by
            linarith
          have h11 : (q : ℚ) = (1 : ℚ) := by
            exact_mod_cast h1
          rw [h11] at hq
          norm_num at hq
        field_simp [h93, h94]
        nlinarith [sq_nonneg ((x : ℝ) * (q : ℝ) - (q - 1 : ℝ)), sq_nonneg ((x : ℝ) * (q - 1 : ℝ) + 1), sq_pos_of_ne_zero (show (q : ℝ) ≠ 0 by
          exact_mod_cast (show q ≠ (0 : ℚ) by
            by_contra h
            have hr0 : q = (0 : ℚ) := by
              exact_mod_cast h
            rw [hr0] at hq
            norm_num at hq
          )
        ), sq_pos_of_ne_zero (show (q - 1 : ℝ) ≠ 0 by
          intro h0
          have h1 : (q : ℝ) = 1 := by
            linarith
          have h11 : (q : ℚ) = (1 : ℚ) := by
            exact_mod_cast h1
          rw [h11] at hq
          norm_num at hq
        )
        ]
      cases' (mul_eq_zero.mp eq92) with eq93 eq94
      · left
        field_simp [(show (q : ℝ) ≠ 0 by
          have eq2 : q ≠ (0 : ℚ) := by
            by_contra h
            have hr0 : q = (0 : ℚ) := by
              exact_mod_cast h
            rw [hr0] at hq
            norm_num at hq
          exact_mod_cast eq2
        )] at eq93 ⊢
        all_goals
          linarith
      · right
        field_simp [(show (q - 1 : ℝ) ≠ 0 by
          intro h0
          have h1 : (q : ℝ) = 1 := by
            linarith
          have h11 : (q : ℚ) = (1 : ℚ) := by
            exact_mod_cast h1
          rw [h11] at hq
          norm_num at hq
        )] at eq94 ⊢
        all_goals
          linarith
    cases eq20 with
    | inl h0 =>
      have eq0 : ∃ r : ℚ, (x : ℝ) = (r : ℝ) := by
        use (q - 1) / q
        exact_mod_cast h0
      exact eq0
    | inr h0 =>
      have eq0 : ∃ r : ℚ, (x : ℝ) = (r : ℝ) := by
        use -1 / (q - 1)
        exact_mod_cast h0
      exact eq0