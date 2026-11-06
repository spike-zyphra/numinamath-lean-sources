import Mathlib

theorem algebra_220264 (a b : ℝ) (h : a + b = 2) :
    (min (abs a) (abs b) < 1 ∧ 1 < max (abs a) (abs b)) ↔ a * b ∈ Set.Ioo (-3) 1 := by
  constructor
  · -- Assume that min (|a|,|b|) < 1 and 1 < max (|a|,|b|).
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : abs a < 1 ∨ abs b < 1 := by
      by_contra h4
      push_neg at h4
      have h5 : abs a ≥ 1 := by linarith
      have h6 : abs b ≥ 1 := by linarith
      have h7 : min (abs a) (abs b) ≥ 1 := by
        cases min_cases (abs a) (abs b) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      linarith
    have h4 : abs a > 1 ∨ abs b > 1 := by
      by_contra h5
      push_neg at h5
      have h6 : abs a ≤ 1 := by linarith
      have h7 : abs b ≤ 1 := by linarith
      have h8 : max (abs a) (abs b) ≤ 1 := by
        cases max_cases (abs a) (abs b) with
        | inl h =>
          linarith
        | inr h =>
          linarith
      linarith
    rcases h3 with (ha1 | hb1)
    · -- Assume |a| < 1
      have h7 : -1 < a := by
        linarith [abs_lt.mp ha1]
      have h8 : a < 1 := by
        linarith [abs_lt.mp ha1]
      rcases h4 with (ha | hb)
      · -- Assume |a| > 1
        have h9 : a < -1 ∨ a > 1 := by
          cases (abs_cases a) with
          | inl h1 =>
            right
            linarith
          | inr h1 =>
            left
            linarith
        rcases h9 with (ha11 | ha22)
        · -- Assume a < -1
          nlinarith
        · -- Assume a > 1
          nlinarith
      · -- Assume |b| > 1
        have h9 : b < -1 ∨ b > 1 := by
          cases (abs_cases b) with
          | inl h1 =>
            right
            linarith
          | inr h1 =>
            left
            linarith
        rcases h9 with (hb11 | hb22)
        · -- Assume b < -1
          nlinarith
        · -- Assume b > 1
          have h13 : b > 1 := by linarith
          have h14 : a * b > -3 := by
            have h15 : b = 2 - a := by linarith
            rw [h15]
            nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (b - 1), sq_nonneg (a - (-1)), sq_nonneg (b - 3)]
          have h15 : a * b < 1 := by
            have h16 : b = 2 - a := by linarith
            rw [h16]
            nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (b - 1), sq_nonneg (a - (-1)), sq_nonneg (b - 3)]
          constructor <;> nlinarith
    · -- Assume |b| < 1
      have h7 : -1 < b := by
        linarith [abs_lt.mp hb1]
      have h8 : b < 1 := by
        linarith [abs_lt.mp hb1]
      rcases h4 with (ha | hb)
      · -- Assume |a| > 1
        have h9 : a < -1 ∨ a > 1 := by
          cases (abs_cases a) with
          | inl h1 =>
            right
            linarith
          | inr h1 =>
            left
            linarith
        rcases h9 with (ha11 | ha22)
        · -- Assume a < -1
          nlinarith
        · -- Assume a > 1
          have h13 : a > 1 := by linarith
          have h14 : a * b > -3 := by
            rw [show b = 2 - a by linarith]
            nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a - 3), sq_nonneg ((2 - a) + 1), sq_nonneg ((2 - a) - 1)]
          have h15 : a * b < 1 := by
            rw [show b = 2 - a by linarith]
            nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a - 3), sq_nonneg ((2 - a) + 1), sq_nonneg ((2 - a) - 1)]
          constructor <;> nlinarith
      · -- Assume |b| > 1
        have h9 : b < -1 ∨ b > 1 := by
          cases (abs_cases b) with
          | inl h1 =>
            right
            linarith
          | inr h1 =>
            left
            linarith
        rcases h9 with (hb11 | hb22)
        · -- Assume b < -1
          nlinarith
        · -- Assume b > 1
          have h13 : a = 2 - b := by linarith
          rw [h13]
          have h14 : (2 - b) * b > -3 := by
            nlinarith [sq_nonneg (b - 1), sq_nonneg (b - 3), sq_nonneg (b - (-1)), sq_nonneg (b - 2)]
          have h15 : (2 - b) * b < 1 := by
            nlinarith [sq_nonneg (b - 1), sq_nonneg (b - 3), sq_nonneg (b - (-1)), sq_nonneg (b - 2)]
          constructor <;> nlinarith
  · -- Assume that a * b ∈ (-3,1)
    rintro ⟨h1, h2⟩
    have h3 : abs a < 1 ∨ abs b < 1 := by
      by_contra h4
      push_neg at h4
      have h4 : abs a ≥ 1 := by linarith
      have h5 : abs b ≥ 1 := by linarith
      cases' abs_cases a with ha ha <;> cases' abs_cases b with hb hb <;> 
        all_goals 
          nlinarith
    have h4 : abs a > 1 ∨ abs b > 1 := by
      by_contra h5
      push_neg at h5
      have h4 : abs a ≤ 1 := by linarith
      have h5 : abs b ≤ 1 := by linarith
      cases' abs_cases a with ha ha <;> cases' abs_cases b with hb hb <;> 
        all_goals
          nlinarith
    constructor
    · -- Show that min (abs a) (abs b) < 1
      cases' h3 with h1 h2
      · -- Assume abs a < 1
        have h3 : abs a < 1 := h1
        have h4 : min (abs a) (abs b) < 1 := by
          cases' min_cases (abs a) (abs b) with h5 h5 
          · -- Case |a| ≤ |b|, so min (|a|, |b|) = |a| 
            linarith
          · -- Case |b| < |a|, so min (|a|, |b|) = |b| 
            linarith
        linarith
      · -- Assume abs b < 1
        have h4 : abs b < 1 := h2
        have h5 : min (abs a) (abs b) < 1 := by
          cases' min_cases (abs a) (abs b) with h6 h6
          · -- Case |a| ≤ |b|, so min (|a|, |b|) = |a| 
            linarith
          · -- Case |b| < |a|, so min (|a|, |b|) = |b| 
            linarith
        linarith
    · -- Show that 1 < max (abs a) (abs b)
      cases' h4 with h1 h2
      · -- Assume abs a > 1
        have h3 : abs a > 1 := h1
        have h4 : max (abs a) (abs b) > 1 := by
          cases' max_cases (abs a) (abs b) with h5 h5
          · -- Case |a| ≥ |b|, so max (|a|, |b|) = |a|
            linarith
          · -- Case |b| > |a|, so max (|a|, |b|) = |b|
            linarith
        linarith
      · -- Assume abs b > 1
        have h4 : abs b > 1 := h2
        have h5 : max (abs a) (abs b) > 1 := by
          cases' max_cases (abs a) (abs b) with h6 h6
          · -- Case |a| ≥ |b|, so max (|a|, |b|) = |a|
            linarith
          · -- Case |b| > |a|, so max (|a|, |b|) = |b|
            linarith
        linarith