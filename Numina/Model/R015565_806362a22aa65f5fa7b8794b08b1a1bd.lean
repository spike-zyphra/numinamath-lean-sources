import Mathlib

theorem algebra_214012 (x y : ℤ) (h : 6*x^2+5*x*y+y^2=6*x+2*y+7) :
    |x|+|y| ≤ |(-8)|+|25| ∧ (|x|+|y| = |(-8)|+|25| ↔ x=-8 ∧ y=25) := by
  have h1 : (3 * x + y) * (2 * x + y - 2) = 7 := by
    nlinarith [h]
  have h2 : (3 * x + y = 1 ∧ 2 * x + y - 2 = 7) ∨
           (3 * x + y = 7 ∧ 2 * x + y - 2 = 1) ∨
           (3 * x + y = -1 ∧ 2 * x + y - 2 = -7) ∨
           (3 * x + y = -7 ∧ 2 * x + y - 2 = -1) := by
    have h3 : (3 * x + y) * (2 * x + y - 2) = 7 := h1
    have h4 : (3 * x + y) ∣ 7 := by
      use (2 * x + y - 2)
      all_goals linarith
    have h5 : (3 * x + y) = 1 ∨ (3 * x + y) = 7 ∨ (3 * x + y) = -1 ∨ (3 * x + y) = -7 := by
      have h4' : (3 * x + y) ∣ 7 := h4
      have h8 : (3 * x + y) ≤ 7 := by
        exact Int.le_of_dvd (by norm_num) h4'
      have h9 : (3 * x + y) ≥ -7 := by
        have h10 : -(3 * x + y) ∣ 7 := by 
          exact Int.neg_dvd.2 h4'
        have h11 : -(3 * x + y) ≤ 7 := by
          exact Int.le_of_dvd (by norm_num) h10
        linarith
      interval_cases h10 : (3 * x + y) <;> omega
    cases h5 with
    | inl h10 =>
      left
      have h20 : 2 * x + y - 2 = 7 := by
        rw [h10] at h3
        linarith
      exact ⟨h10, h20⟩
    | inr h5 =>
      cases h5 with
      | inl h10 =>
        right
        left
        have h20 : 2 * x + y - 2 = 1 := by
          rw [h10] at h3
          linarith
        exact ⟨h10, h20⟩
      | inr h5 =>
        cases h5 with
        | inl h10 =>
          right
          right
          left
          have h20 : 2 * x + y - 2 = -7 := by
            rw [h10] at h3
            linarith
          exact ⟨h10, h20⟩
        | inr h10 =>
          right
          right
          right
          have h20 : 2 * x + y - 2 = -1 := by
            rw [h10] at h3
            linarith
          exact ⟨h10, h20⟩
  cases h2 with
  | inl h3 =>
    have eq1 : 3 * x + y = 1 := by linarith
    have eq2 : 2 * x + y - 2 = 7 := by linarith
    have hx1 : x = -8 := by 
      omega
    have hy1 : y = 25 := by
      linarith [hx1, eq1]
    constructor
    · -- Show that |x| + |y| ≤ |(-8)| + |25|
      rw [hx1, hy1]
      all_goals norm_num
    · -- Show that |x| + |y| = |(-8)| + |25| ↔ x = -8 ∧ y = 25
      constructor
      · -- Forward direction
        intro h_eq
        rw [hx1, hy1] at h_eq
        norm_num at h_eq
        tauto
      · -- Backward direction
        rintro ⟨rfl, rfl⟩
        all_goals norm_num
  | inr h2 =>
    cases h2 with
    | inl h3 =>
      have eq1 : 3 * x + y = 7 := by linarith
      have eq2 : 2 * x + y - 2 = 1 := by linarith
      have hx1 : x = 4 := by 
        omega
      have hy1 : y = -5 := by 
        linarith [hx1, eq1]
      constructor
      · -- Show that |x| + |y| ≤ |(-8)| + |25|
        rw [hx1, hy1]
        all_goals norm_num
      · -- Show that |x| + |y| = |(-8)| + |25| ↔ x = -8 ∧ y = 25
        constructor
        · -- Forward direction: if |x| + |y| = |(-8)| + |25|, then x = -8 ∧ y = 25
          intro h_eq
          rw [hx1, hy1] at h_eq
          norm_num at h_eq
          all_goals exfalso <;> omega
        · -- Backward direction: if x = -8 ∧ y = 25, then |x| + |y| = |(-8)| + |25|
          rintro ⟨rfl, rfl⟩
          all_goals norm_num
    | inr h2 =>
      cases h2 with
      | inl h3 =>
        have eq1 : 3 * x + y = -1 := by linarith
        have eq2 : 2 * x + y - 2 = -7 := by linarith
        have hx1 : x = 4 := by 
          omega
        have hy1 : y = -13 := by 
          linarith [hx1, eq1]
        constructor
        · -- Show that |x| + |y| ≤ |(-8)| + |25|
          rw [hx1, hy1]
          all_goals norm_num
        · -- Show that |x| + |y| = |(-8)| + |25| ↔ x = -8 ∧ y = 25
          constructor
          · -- Forward direction: if |x| + |y| = |(-8)| + |25|, then x = -8 ∧ y = 25
            intro h_eq
            rw [hx1, hy1] at h_eq
            norm_num at h_eq
            all_goals exfalso <;> omega
          · -- Backward direction: if x = -8 ∧ y = 25, then |x| + |y| = |(-8)| + |25|
            rintro ⟨rfl, rfl⟩
            all_goals norm_num
      | inr h3 =>
        have eq1 : 3 * x + y = -7 := by linarith
        have eq2 : 2 * x + y - 2 = -1 := by linarith
        have hx1 : x = -8 := by 
          omega
        have hy1 : y = 17 := by 
          linarith [hx1, eq1]
        constructor
        · -- Show that |x| + |y| ≤ |(-8)| + |25|
          rw [hx1, hy1]
          all_goals norm_num
        · -- Show that |x| + |y| = |(-8)| + |25| ↔ x = -8 ∧ y = 25
          constructor
          · -- Forward direction: if |x| + |y| = |(-8)| + |25|, then x = -8 ∧ y = 25
            intro h_eq
            rw [hx1, hy1] at h_eq
            norm_num at h_eq
            all_goals exfalso <;> omega
          · -- Backward direction: if x = -8 ∧ y = 25, then |x| + |y| = |(-8)| + |25|
            rintro ⟨rfl, rfl⟩
            all_goals norm_num