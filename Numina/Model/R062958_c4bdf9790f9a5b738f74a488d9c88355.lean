import Mathlib

theorem algebra_237449 (x : ℝ) : ⌊(5 + 6 * x) / 8⌋ = (15 * x - 7) / 5 ↔
    x = 7 / 15 ∨ x = 4 / 5 := by
  constructor
  · -- Forward direction: if ⌊(5 + 6 * x) / 8⌋ = (15 * x - 7) / 5 then x = 7 / 15 or x = 4 / 5
    intro h_eq
    let n := ⌊(5 + 6 * x) / 8⌋
    have hn1 : (n : ℝ) = (15 * x - 7) / 5 := by
      exact_mod_cast h_eq
    have h1 : (n : ℝ) ≤ (5 + 6 * x) / 8 := by
      exact_mod_cast Int.floor_le ( (5 + 6 * x) / 8 )
    have h2 : (5 + 6 * x) / 8 < (n + 1 : ℝ) := by
      exact_mod_cast Int.lt_floor_add_one ( (5 + 6 * x) / 8 )
    have hx : x = (5 * (n : ℝ) + 7) / 15 := by
      nlinarith
    rw [hx] at h1
    rw [hx] at h2
    have : n = 0 ∨ n = 1 := by 
      have h3 : (n : ℝ) ≤ (39 + 10 * (n : ℝ)) / 40 := by 
        nlinarith 
      have h4 : (39 + 10 * (n : ℝ)) / 40 < (↑n + 1 : ℝ) := by 
        nlinarith 
      have h5 : n ≤ 1 := by 
        by_contra h 
        push_neg at h 
        have h6 : n ≥ 2 := by 
          omega 
        have h7 : (n : ℝ) ≥ (2 : ℝ) := by 
          exact_mod_cast h6 
        nlinarith 
      have h6 : n ≥ 0 := by 
        by_contra h 
        push_neg at h 
        have h7 : n ≤ -1 := by 
          omega 
        have h8 : (n : ℝ) ≤ (-1 : ℝ) := by 
          exact_mod_cast h7 
        -- Exploiting the fact that n ≥ -1 from our initial constraints
        nlinarith 
      interval_cases n <;> norm_num at *
      <;> omega 
    cases this with
    | inl hn0 => 
      have hx0 : x = 7 / 15 := by 
        have : (n : ℝ) = (0 : ℝ) := by 
          exact_mod_cast hn0 
        rw [this] at hx 
        nlinarith 
      left 
      exact hx0 
    | inr hn1 => 
      have hx1 : x = 4 / 5 := by 
        have : (n : ℝ) = (1 : ℝ) := by 
          exact_mod_cast hn1 
        rw [this] at hx 
        nlinarith 
      right 
      exact hx1 
  · -- Backward direction: if x = 7 / 15 or x = 4 / 5 then ⌊(5 + 6 * x) / 8⌋ = (15 * x - 7) / 5
    rintro (rfl | rfl)
    · -- Case x = 7 / 15
      norm_num 
      <;> try { native_decide }
    · -- Case x = 4 / 5
      norm_num 
      <;> try { native_decide }