import Mathlib

def f (x : ℝ) := x ^ 2 + 3

lemma lemma_1 : StrictMonoOn f (Set.Ici 0) := by -- Fundamental Theorem: f (x) monotonically increases at [0,+∞)
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := by
    simpa using hx
  have hy0 : 0 ≤ y := by
    simpa using hy
  have h1 : x ^ 2 ≤ y ^ 2 := by nlinarith
  simp [f]
  nlinarith

lemma lemma_2 : StrictMonoOn f^[10] (Set.Ici 0) := by -- Then f ^ [10] x monotonically increases at [0,+∞)
  have h1 : StrictMonoOn f (Set.Ici 0) := lemma_1
  intro x hx y hy hxy
  have h3 : ∀ (n : ℕ), f^[n] x < f^[n] y := by
    intro n
    induction n with
    | zero =>
      simp
      all_goals linarith
    | succ n ih =>
      have h4 : f^[n + 1] x = f (f^[n] x) := by
        simp [Function.iterate_succ_apply']
      have h5 : f^[n + 1] y = f (f^[n] y) := by
        simp [Function.iterate_succ_apply']
      rw [h4, h5]
      have h6 : f^[n] x ≥ 0 := by
        have h6 : ∀ (k : ℕ), f^[k] x ≥ 0 := by
          intro k
          induction k with
          | zero =>
            simp at hx ⊢
            all_goals linarith
          | succ k ih =>
            have h7 : f^[k + 1] x = f (f^[k] x) := by
              simp [Function.iterate_succ_apply']
            rw [h7]
            have hx1 : f^[k] x ≥ 0 := ih
            have hx2 : f^[k] x ^ 2 ≥ 0 := by nlinarith
            simp [f]
            nlinarith
        exact h6 n
      have h7 : f^[n] y ≥ 0 := by
        have h7 : ∀ (k : ℕ), f^[k] y ≥ 0 := by
          intro k
          induction k with
          | zero =>
            simp at hy ⊢
            all_goals linarith
          | succ k ih =>
            have h8 : f^[k + 1] y = f (f^[k] y) := by
              simp [Function.iterate_succ_apply']
            rw [h8]
            have hy1 : f^[k] y ≥ 0 := ih
            have hy2 : f^[k] y ^ 2 ≥ 0 := by nlinarith
            simp [f]
            nlinarith
        exact h7 n
      have h8 : f (f^[n] x) < f (f^[n] y) := by
        apply h1
        all_goals
          try { simpa using h6 }
          try { simpa using h7 }
          try { simpa using ih }
      simpa using h8
  have hx10 : f^[10] x < f^[10] y := h3 10
  simpa using hx10

lemma lemma_3 (x : ℝ) : f^[10] x = f^[10] (-x) := by -- f ^ [10] is an even function
  repeat rw [show ∀ x : ℝ, f^[10] x = f^[9] (f x) by simp]
  rw [show f x = f (-x) by unfold f; simp]

lemma lemma_4 (x y : ℝ) : f^[10] x = f^[10] y ↔ x = y ∨ x = - y := by -- The property of equality in the f ^ [10] equation
  constructor
  case mpr
  . intro h
    match h with
    | Or.inr h =>
      rw [h]
      exact (lemma_3 y).symm
    | Or.inl h =>
      rw [h]
  case mp
  . intro h
    if hx : x ≥ 0 then -- Conduct classified discussions
    . if hy : y ≥ 0 then
      . apply Or.intro_left
        exact StrictMonoOn.injOn lemma_2 hx hy h
      else
      . apply Or.intro_right
        rw [lemma_3 y] at h
        have hy' : -y≥0 := by linarith
        exact StrictMonoOn.injOn lemma_2 hx hy' h
    else
    . if hy : y ≥ 0 then
      . apply Or.intro_right
        rw [lemma_3 x] at h
        have hx' : -x≥0 := by linarith
        have := StrictMonoOn.injOn lemma_2 hx' hy h
        linarith
      else
      . apply Or.intro_left
        rw [lemma_3 x, lemma_3 y] at h
        have hx' : -x≥0 := by linarith
        have hy' : -y≥0 := by linarith
        have := StrictMonoOn.injOn lemma_2 hx' hy' h
        linarith

theorem algebra_211339 (x : ℝ) : f^[10] (7 * x - 3) = f^[11] x ↔ x = -7 ∨ x = 0 ∨ x = 1 ∨ x = 6 := by
  rw [show ∀x:ℝ,f^[11] x = f^[10] (f x) by simp]
  rw [lemma_4]
  unfold f
  constructor
  case mpr
  . intro h
    rcases h with h|h|h|h
    repeat rw [h]; norm_num
  case mp
  . intro h
    rcases h with h|h
    . --  h : 7 * x - 3 = x ^ 2 + 3
      apply Or.intro_right
      apply Or.intro_right
      have h1 : x^2 - 7 * x + 6 = 0 := by linarith
      have h2 : (x - 1) * (x - 6) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h2) with h3 h4
      · -- Case \(x - 1 = 0\), so \(x = 1\).
        left
        linarith
      · -- Case \(x - 6 = 0\), so \(x = 6\).
        right
        linarith
    . -- h : 7 * x - 3 = -(x ^ 2 + 3)
      have h2 : x * (x + 7) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h2) with h3 h4
      · -- Case x = 0.
        right;left
        exact h3
      · -- Case x+7=0
        left
        linarith
