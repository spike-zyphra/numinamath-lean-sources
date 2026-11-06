import Mathlib

/- Given the function $y=|\sin^2x-4\sin x-a|$ has a maximum value of $4$, find the constant $a=$ ______. -/
theorem algebra_9040 (a : ℝ) (f : ℝ → ℝ) (hf : f = fun x => abs (Real.sin x ^ 2 - 4 * Real.sin x - a)) : IsGreatest (Set.image f {x | x ∈ Set.univ}) 4 ↔ a = 1 := by
  rw [IsGreatest, upperBounds]
  simp
  -- we can prove f(x) = |(sinx-2)^2-(4+a)|
  have hf': f = fun x => (|(Real.sin x - 2)^2 - (4+a)|) := by
    rw [hf]
    funext x
    have: Real.sin x ^ 2 - 4 * Real.sin x - a = (Real.sin x - 2)^2 - (4+a) := by ring
    rw [this]
  -- depends on (Real.sin x - 2) ^ 2 ≥ a+4 or not, the maximum value of f(x) has two possible values.
  have hfle: ∀x:ℝ, f x ≤ max (5-a) (a+3) := by
    rw [hf']
    intro x
    simp
    by_cases hcases: (Real.sin x - 2) ^ 2 ≥ a+4
    -- prove (Real.sin x - 2) ^ 2 - (4 + a) ≤ 5-a
    have ht1: |(Real.sin x - 2) ^ 2 - (4 + a)| = (Real.sin x - 2)^2 - (4+a) := by
      have: 0 ≤ (Real.sin x - 2)^2 - (4+a) := by linarith [hcases]
      exact abs_of_nonneg this
    have ht2: (Real.sin x - 2)^2 ≤ 9 := by
      have: (9:ℝ) = 3^2 := by norm_num
      rw [this]
      have h11: -3 ≤ Real.sin x - 2 := by
        have: -1 ≤ Real.sin x := Real.neg_one_le_sin x
        linarith [this]
      have h22: Real.sin x - 2 ≤ 3 := by
        have: Real.sin x ≤ 1 := Real.sin_le_one x
        linarith [this]
      apply sq_le_sq' h11 h22
    rw [ht1]
    have: (Real.sin x - 2) ^ 2 - (4 + a) ≤ 5-a := by
      have htt1: (Real.sin x - 2) ^ 2 - (4 + a) ≤ 9 - (4+a) := by
        linarith [ht2]
      have: 9 - (4+a) = 5-a := by ring
      rwa [this] at htt1
    exact Or.symm (Or.inr this)
    -- prove |(Real.sin x - 2) ^ 2 - (4 + a)| ≤ a+3
    push_neg at hcases
    have ht1: |(Real.sin x -2)^2-(4+a)| = - ((Real.sin x - 2)^2 - (4+a)) := by
      have: (Real.sin x -2)^2-(4+a) ≤ 0 := by linarith [hcases]
      exact abs_of_nonpos this
    have ht2:  -((Real.sin x - 2) ^ 2 - (4 + a)) ≤ a+3 := by
      have: (Real.sin x - 2)^2 ≥ 1 := by
        have: (1:ℝ) = 1^2 := by norm_num
        rw [this]
        have: |Real.sin x - 2| ≥ |1| := by
          have: |Real.sin x - 2| = |2-Real.sin x| := by
            have: Real.sin x - 2 = -(2-Real.sin x) := by ring
            rw [this]
            exact abs_neg (2 - Real.sin x)
          rw [this]
          have: Real.sin x ≤ 1 := Real.sin_le_one x
          have htt1: 1 ≤ 2 - Real.sin x := by
            linarith [this]
          have htt2: -1 ≤ 2 - Real.sin x:= by
            linarith [this]
          apply abs_le_abs htt1 htt2
        exact sq_le_sq.mpr this
      linarith [this]
    rw [ht1]
    right
    exact ht2
  have hfex: ∃x:ℝ, f x = max (5-a) (a+3) := by
    rw [hf']
    simp
    by_cases hcases: 5-a ≥ a+3
    have h1: max (5 - a) (a + 3) = 5-a := max_eq_left hcases
    have h2: 0 ≤ 5-a := by linarith [hcases]
    use (-(Real.pi/2))
    have: (-1 - 2) ^ 2 - (4 + a) = 5-a := by ring
    simp [this]
    rw [h1]
    exact abs_of_nonneg h2
    push_neg at hcases
    have h1: max (5 - a) (a + 3) = a+3 := max_eq_right_of_lt hcases
    use (Real.pi/2)
    simp
    have: (1 - 2) ^ 2 - (4 + a) = -(a+3) := by ring
    rw [this, h1]
    have: 0 ≤ a+3 := by linarith [hcases]
    have h2: a+3 = |a+3| := Eq.symm (abs_of_nonneg this)
    have h3: |(-(a + 3))| = |a+3| := abs_neg (a + 3)
    rw [h3]
    nth_rw 2 [h2]
  constructor
  -- mp direction. f(x) has max value of 4, prove a = 1.
  intro ⟨fex, fmax⟩
  -- we have maximum value of f(x) is max(5-a)(a+3) and 4, thus they must  be equal.
  have h1: max (5-a) (a+3) = 4 := by
    have ht1: max (5-a) (a+3) ≤ 4 := by
      rcases hfex with ⟨x0, h1x0⟩
      rcases fmax x0 with h2x0
      rwa [h1x0] at h2x0
    have ht2: 4 ≤ max (5-a) (a+3) := by
      rcases fex with ⟨x0, h1x0⟩
      rcases hfle x0 with h2x0
      rwa [h1x0] at h2x0
    symm
    apply eq_of_le_of_le ht2 ht1
  by_cases hcase: a+3 ≤ 5-a
  have: max (5 - a) (a + 3) = 5-a := max_eq_left hcase
  rw [this] at h1
  linarith [h1]
  push_neg at hcase
  have: max (5-a) (a+3) = a+3 := max_eq_right_of_lt hcase
  rw [this] at h1
  linarith [h1]
  -- mpr direction. given a=1, find maximum value of f(x)
  -- substitue a=1 back
  intro aeq
  have: max (5 - 1:ℝ) (1 + 3:ℝ) = 4 := by
    have ht1: (5-1:ℝ) = 4 := by norm_num
    have ht2: (1+3:ℝ) = 4 := by norm_num
    rw [ht1,ht2]
    simp
  rw [aeq, this] at hfle
  rw [aeq, this] at hfex
  exact ⟨hfex, hfle⟩