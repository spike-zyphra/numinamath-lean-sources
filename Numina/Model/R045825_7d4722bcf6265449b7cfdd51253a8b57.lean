import Mathlib


open Real


theorem algebra_98439 :
    IsGreatest ((fun (a, b, _) ↦ a + b) '' {(a, b, q) : ℕ × ℕ × ℕ |
      a ∈ Set.Ioc 0 q ∧ b ∈ Set.Ioc 0 (500 - q) ∧
      (a / q : ℝ) < 160 / 300 ∧ (b / (500 - q) : ℝ) < 140 / 200}) 349 ∧
    Nat.Coprime 349 500 ∧ 349 + 500 = 849 := by
  constructor
  · -- Show 349 is greatest in the image.
    constructor
    · -- First show 349 is attained.
      use (1, 348, 2)
      norm_num [Set.mem_Ioc]
    · -- Show that 349 is greatest.
      intro x hx
      rcases hx with ⟨⟨a, b, q⟩, h, rfl⟩
      rcases h with ⟨ha, hb, ha1, hb1⟩
      rcases ha with ⟨ha0, ha2⟩
      rcases hb with ⟨hb0, hb2⟩
      have h1 : (a : ℝ) / (q : ℝ) < (160 / 300 : ℝ) := by
        simpa using ha1
      have h2 : (b : ℝ) / ((500 - q) : ℝ) < (140 / 200 : ℝ) := by
        simpa using hb1
      have h3 : q > 0 := by
        by_contra h
        have h4 : q = 0 := by
          omega
        rw [h4] at h1 ha2
        norm_num at h1
        all_goals try { linarith }
      have h4 : q ≤ 500 := by
        omega
      have h349 : a + b ≤ 349 := by
        by_contra h
        push_neg at h
        have h4 : a + b ≥ 350 := by
          omega
        have h5 : (a : ℝ) + (b : ℝ) ≥ (350 : ℝ) := by
          exact_mod_cast h4
        have h300 : (a : ℝ) < (160 / 300 : ℝ) * (q : ℝ) := by
          have h340 : (a : ℝ) / (q : ℝ) < (160 / 300 : ℝ) := h1
          have h350 : (q : ℝ) > 0 := by
            exact_mod_cast show (0 : ℝ) < q by
              exact_mod_cast h3
          have h360 : (a : ℝ) < (160 / 300 : ℝ) * (q : ℝ) := by
            have h370 : (a : ℝ) / (q : ℝ) < (160 / 300 : ℝ) := h1
            apply (div_lt_iff₀ (by positivity)).mp at h370
            linarith
          linarith
        have h400 : (b : ℝ) < (140 / 200 : ℝ) * ((500 - q) : ℝ) := by
          have h440 : (b : ℝ) / ((500 - q) : ℝ) < (140 / 200 : ℝ) := h2
          have h0 : (500 - q : ℝ) > 0 := by
            have h0 : (500 - q : ℕ) > 0 := by
              omega
            exact_mod_cast h0
          have h460 : (b : ℝ) < (140 / 200 : ℝ) * ((500 - q) : ℝ) := by
            have h470 : (b : ℝ) / ((500 - q) : ℝ) < (140 / 200 : ℝ) := h2
            have h0 : (500 - q : ℝ) > 0 := by
              have h0 : (500 - q : ℕ) > 0 := by
                omega
              exact_mod_cast h0
            apply (div_lt_iff₀ (by positivity)).mp at h470
            linarith
          linarith
        have h600 : (a : ℝ) + (b : ℝ) < (160 / 300 : ℝ) * (q : ℝ) + (140 / 200 : ℝ) * ((500 - q) : ℝ) := by
          linarith
        nlinarith [sq_nonneg ((q : ℝ) - (2 : ℝ)), sq_nonneg ((500 - q : ℝ) - (498 : ℝ)), sq_nonneg ((a : ℝ) - (1 : ℝ)), sq_nonneg ((b : ℝ) - (348 : ℝ)), (show (0 : ℝ) < (160 / 300 : ℝ) by norm_num), (show (0 : ℝ) < (140 / 200 : ℝ) by norm_num)]
      linarith
  constructor
  · -- Show 349 and 500 are coprime.
    norm_num
  · -- Show 349 + 500 = 849.
    norm_num