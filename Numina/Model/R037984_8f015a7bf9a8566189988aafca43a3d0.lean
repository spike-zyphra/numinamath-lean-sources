import Mathlib

theorem algebra_9332 {a : ℝ} (f : ℝ → ℝ) (f_def : f = fun x => x ^ 2 + a * x) :
    (∃ y_min, (∀ x, y_min ≤ f x) ∧ (∃ x, y_min = f x) ∧ (∀ x, y_min ≤ f (f x)) ∧ (∃ x, y_min = f (f x))) ↔ a ≤ 0 ∨ a ≥ 2 := by
  constructor
  · -- Forward implication: If such a y exists, then a ≤ 0 or a ≥ 2
    intro h
    rcases h with ⟨y_min, hy1, hy2, hy3, hy4⟩
    have h1 : ∀ x, y_min ≤ x ^ 2 + a * x := by
      intro x
      specialize hy1 x
      simp [f_def] at hy1 ⊢
      linarith
    have h2 : ∃ x, y_min = x ^ 2 + a * x := by
      rcases hy2 with ⟨x, hx⟩
      simp [f_def] at hx ⊢
      exact ⟨x, hx⟩
    have h3 : ∀ x, y_min ≤ (x ^ 2 + a * x) ^ 2 + a * (x ^ 2 + a * x) := by
      intro x
      specialize hy3 x
      simp [f_def] at hy3 ⊢
      linarith
    have h4 : ∃ x, y_min = (x ^ 2 + a * x) ^ 2 + a * (x ^ 2 + a * x) := by
      rcases hy4 with ⟨x, hx⟩
      simp [f_def] at hx ⊢
      exact ⟨x, hx⟩
    have h5 : y_min = -a ^ 2 / 4 := by
      have h6 := h1 (-a / 2)
      ring_nf at h6
      rcases h2 with ⟨x, h7⟩
      have h8 : x ^ 2 + a * x ≥ -a ^ 2 / 4 := by
        nlinarith [sq_nonneg (x + a / 2)]
      nlinarith
    rcases h4 with ⟨y, h6⟩
    have h14 : (y ^ 2 + a * y) ^ 2 + a * (y ^ 2 + a * y) = -a ^ 2 / 4 := by
      nlinarith [h5, h6]
    have h10 : y ^ 2 + a * y = -a / 2 := by
      have h11 : (y ^ 2 + a * y) ^ 2 + a * (y ^ 2 + a * y) + a ^ 2 / 4 = 0 := by
        nlinarith
      have h12 : (y ^ 2 + a * y + a / 2) ^ 2 = 0 := by
        nlinarith
      have h12' : y ^ 2 + a * y + a / 2 = 0 := by
        nlinarith
      linarith
    -- Solving the discriminant from the existence of such a y.
    have h13 : a * (a - 2) ≥ 0 := by
      nlinarith [sq_nonneg (y + a / 2)]
    by_cases ha1 : a ≤ 0
    · -- Case a ≤ 0
      tauto
    · -- Case a > 0
      have ha2 : a > 0 := by nlinarith
      right
      nlinarith
  · -- Backward implication: If a ≤ 0 or a ≥ 2, then such a y exists
    rintro (ha | ha)
    · -- Case a ≤ 0
      use -a ^ 2 / 4
      constructor
      · -- Show that y_min is a lower bound for f(x)
        intro x
        simp [f_def]
        nlinarith [sq_nonneg (x + a / 2)]
      constructor
      · -- Show that there exists some x such that y_min = f(x)
        use -a / 2
        simp [f_def]
        <;> ring_nf <;> nlinarith
      constructor
      · -- Show that y_min is a lower bound for f(f(x))
        intro x
        simp [f_def]
        nlinarith [sq_nonneg (x + a / 2), sq_nonneg (x ^ 2 + a * x + a / 2), sq_nonneg ((x ^ 2 + a * x) + a / 2), sq_nonneg ((x + a / 2) ^ 2), sq_nonneg (a * (x + a / 2)), sq_nonneg (a - 2)]
      · -- Show that there exists some x such that y_min = f(f(x))
        have h14 : a ^ 2 - 2 * a ≥ 0 := by nlinarith
        have h17 : ∃ x : ℝ, x ^ 2 + a * x = -a / 2 := by
          use (-a + Real.sqrt (a ^ 2 - 2 * a)) / 2
          have h51 : Real.sqrt (a ^ 2 - 2*a) ^ 2 = a ^ 2 - 2 * a := Real.sq_sqrt (by nlinarith)
          nlinarith
          <;> norm_num
          <;> nlinarith
        rcases h17 with ⟨x, hx⟩
        use x
        have h10 : (-a ^ 2 / 4) = (x ^ 2 + a * x) ^ 2 + a * (x ^ 2 + a * x) := by
          rw [show x ^ 2 + a * x = -a / 2 by linarith]
          nlinarith
          <;> ring_nf
          <;> nlinarith
        simp [f_def]
        nlinarith
    · -- Case a ≥ 2
      use -a ^ 2 / 4
      constructor
      · -- Show that y_min is a lower bound for f(x)
        intro x
        simp [f_def]
        nlinarith [sq_nonneg (x + a / 2)]
      constructor
      · -- Show that there exists some x such that y_min = f(x)
        use -a / 2
        simp [f_def]
        <;> ring_nf <;> nlinarith
      constructor
      · -- Show that y_min is a lower bound for f(f(x))
        intro x
        simp [f_def]
        nlinarith [sq_nonneg (x + a / 2), sq_nonneg (x ^ 2 + a * x + a / 2), sq_nonneg ((x ^ 2 + a * x) + a / 2), sq_nonneg ((x + a / 2) ^ 2), sq_nonneg (a * (x + a / 2)), sq_nonneg (a - 2)]
      · -- Show that there exists some x such that y_min = f(f(x))
        have h14 : a ^ 2 - 2 * a ≥ 0 := by nlinarith
        have h17 : ∃ x : ℝ, x ^ 2 + a * x = -a / 2 := by
          use (-a + Real.sqrt (a ^ 2 - 2 * a)) / 2
          have h51 : Real.sqrt (a ^ 2 - 2*a) ^ 2 = a ^ 2 - 2 * a := Real.sq_sqrt (by nlinarith)
          nlinarith
          <;> norm_num
          <;> nlinarith
        rcases h17 with ⟨x, hx⟩
        use x
        have h10 : (-a ^ 2 / 4) = (x ^ 2 + a * x) ^ 2 + a * (x ^ 2 + a * x) := by
          rw [show x ^ 2 + a * x = -a / 2 by linarith]
          nlinarith
          <;> ring_nf
          <;> nlinarith
        simp [f_def]
        nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals
  nlinarith
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num
  <;> norm_num