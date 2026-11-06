import Mathlib


open Set


lemma lemma_1 (x y : ℝ) : |y - x| = |x + 1| → y = 2 * x + 1 ∨ y = -1 := by
  intro h_eq
  cases (abs_eq_abs.1 h_eq) with
  | inl h_eq1 =>
    left
    linarith
  | inr h_eq2 =>
    right
    linarith


theorem algebra_150708 (x y : ℝ) :
    abs (y - x) = abs (x + 1) ∧ (y - 3) / 4 = ⌊(x - 1) / 5⌋ ↔
    (x = 1 ∧ y = 3) ∨ (x ∈ Set.Ico (-4) 1 ∧ y = -1) := by
  constructor
  · -- Assume (abs (y - x) = abs (x + 1) ∧ (y - 3) / 4 = ⌊(x - 1) / 5⌋), prove ((x = 1 ∧ y = 3) ∨ (x ∈ Set.Ico (-4) 1 ∧ y = -1))
    rintro ⟨h1, h2⟩
    have h1' : y = 2 * x + 1 ∨ y = -1 := by
      apply lemma_1 x y
      all_goals
        simpa using h1
    cases h1' with
    | inl hy1 =>
      have n_eq : (y - 3) / 4 = (⌊(x - 1) / 5⌋ : ℝ) := by
        simpa using h2
      have eq1' : (x - 1) / 2 = (⌊(x - 1) / 5⌋ : ℝ) := by
        rw [show (y - 3) / 4 = (x - 1) / 2 by
          nlinarith [hy1]
        ] at n_eq
        linarith
      have hn1 : (⌊(x - 1) / 5⌋ : ℝ) ≤ (x - 1) / 5 := by
        exact_mod_cast (Int.floor_le ((x - 1) / 5))
      have hn2 : (⌊(x - 1) / 5⌋ + 1 : ℝ) > (x - 1) / 5 := by
        exact_mod_cast (Int.lt_floor_add_one ((x - 1) / 5))
      have hx5 : x = 2 * (⌊(x - 1) / 5⌋ : ℝ) + 1 := by
        nlinarith
      have h_n1 : ⌊(x - 1) / 5⌋ ≥ -1 := by
        by_contra h
        push_neg at h
        have h_n1 : ⌊(x - 1) / 5⌋ ≤ -2 := by omega
        have hn4 : (⌊(x - 1) / 5⌋ : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast (show (⌊(x - 1) / 5⌋ : ℤ) ≤ (-2 : ℤ) by linarith)
        nlinarith
      have h_n2 : ⌊(x - 1) / 5⌋ ≤ 0 := by
        by_contra h
        push_neg at h
        have h_n2 : ⌊(x - 1) / 5⌋ ≥ 1 := by omega
        have hn5 : (⌊(x - 1) / 5⌋ : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (⌊(x - 1) / 5⌋ : ℤ) ≥ (1 : ℤ) by linarith)
        nlinarith
      have hn3 : ⌊(x - 1) / 5⌋ = -1 ∨ ⌊(x - 1) / 5⌋ = 0 := by
        omega
      rcases hn3 with hn | hn
      · -- ⌊(x - 1) / 5⌋ = -1
        have hn6 : (⌊(x - 1) / 5⌋ : ℝ) = (-1 : ℝ) := by exact_mod_cast hn
        have hx6 : x = -1 := by
          nlinarith [hn6, hx5]
        have hy6 : y = -1 := by
          nlinarith [hy1, hx6]
        right
        constructor
        · -- x ∈ Set.Ico (-4) 1
          exact ⟨by linarith, by linarith⟩
        · -- y = -1
          linarith
      · -- ⌊(x - 1) / 5⌋ = 0
        have hn6 : (⌊(x - 1) / 5⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast hn
        have hx6 : x = 1 := by
          nlinarith [hn6, hx5]
        have hy6 : y = 3 := by
          nlinarith [hy1, hx6]
        left
        exact ⟨by linarith, by linarith⟩
    | inr hy2 =>
          -- Case analysis for the second part. This must result in one side of the final answer.
      have eq1 : (y - 3) / 4 = (⌊(x - 1) / 5⌋ : ℝ) := by
        simpa using h2
      rw [show y = -1 by
        linarith [hy2]
      ] at eq1
      have hn1 : ⌊(x - 1) / 5⌋ = -1 := by
        have h_eq : (⌊(x - 1) / 5⌋ : ℝ) = (-1 : ℝ) := by
          nlinarith -- y = -1 is substituted into h2
        exact_mod_cast h_eq
      have hx1 : -4 ≤ x := by
        have hn3 : -1 ≤ (x - 1) / 5 := by
          have h1 := Int.floor_le ((x - 1) / 5)
          rw [show ⌊(x - 1) / 5⌋ = -1 by exact_mod_cast hn1] at h1
          norm_num at h1 ⊢
          all_goals linarith
        nlinarith
      have hx2 : x < 1 := by
        have hn4 : (x - 1) / 5 < (0 : ℝ) := by
          have h4 := Int.lt_floor_add_one ((x - 1) / 5)
          rw [show ⌊(x - 1) / 5⌋ = -1 by exact_mod_cast hn1] at h4
          norm_num at h4 ⊢
          all_goals linarith
        nlinarith
      right
      constructor
      · -- x ∈ Set.Ico (-4) 1
        exact ⟨by linarith, by linarith⟩
      · -- y = -1
        linarith
  · -- Assume ((x = 1 ∧ y = 3) ∨ (x ∈ Set.Ico (-4) 1 ∧ y = -1)), prove abs (y - x) = abs (x + 1) ∧ (y - 3) / 4 = ⌊(x - 1) / 5⌋ 
    rintro (h | h)
    · -- x = 1 ∧ y = 3
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- First part of conjunction: abs (y - x) = abs (x + 1)
        norm_num [abs]
        <;> nlinarith
      · -- Second part of conjunction: (y - 3) / 4 = ⌊(x - 1) / 5⌋ 
        norm_num 
        <;> try { native_decide }
        <;> simp [Int.floor_eq_iff]
        <;> norm_num 
        <;> try { native_decide }
        all_goals norm_num
    · -- x ∈ Set.Ico (-4) 1 ∧ y = -1
      rcases h with ⟨⟨h1, h2⟩, hy1⟩
      constructor
      · -- First part of conjunction: abs (y - x) = abs (x + 1)
        rw [show y = -1 by linarith]
        cases abs_cases (x + 1) with
        | inl h_eq1 =>
          cases abs_cases (-1 - x) with
          | inl h_eq2 =>
            linarith
          | inr h_eq2 =>
            linarith
        | inr h_eq1 =>
          cases abs_cases (-1 - x) with
          | inl h_eq2 =>
            linarith
          | inr h_eq2 =>
            linarith
        all_goals try nlinarith
      · -- Second part of conjunction: (y - 3) / 4 = ⌊(x - 1) / 5⌋ 
        rw [hy1]
        have h3 : ⌊(x - 1) / 5⌋ = -1 := by
          have h4 : -4 ≤ x := h1
          have h5 : x < 1 := h2
          have hn1 : -5 ≤ x - 1 := by linarith
          have hn2 : x - 1 < 0 := by linarith
          have hn3 : -1 ≤ (x - 1) / 5 := by linarith 
          have hn4 : (x - 1) / 5 < (0 : ℝ) := by linarith 
          have hn5 : ⌊(x - 1) / 5⌋ = -1 := by
            rw [Int.floor_eq_iff]
            constructor <;> (try norm_num) <;> try { nlinarith }
            all_goals nlinarith
          exact_mod_cast hn5
        rw [h3]
        all_goals norm_num
        <;> nlinarith