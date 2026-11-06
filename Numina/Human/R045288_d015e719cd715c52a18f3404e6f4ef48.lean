import Mathlib
/- Let $a, b, c$ be rational numbers such that
$$
\frac{1}{a+b c}+\frac{1}{b+a c}=\frac{1}{a+b}
$$
Prove that $\sqrt{\frac{c-3}{c+1}}$ is also a rational number -/
theorem algebra_606033 (a b c : ℚ) (h : 1 / (a + b * c) + 1 / (b + a * c) = 1 / (a + b)) (h3 : a + b ≠ 0) : ∃ r : ℚ, √((c - 3) / (c + 1)) = ↑r:= by
  -- Case 1: When b + ac = 0
  by_cases h2 : b + a * c = 0
  · simp [h2] at h
    -- Subcase 1.1: When b = 0
    by_cases hb : b = 0
    · -- Prove a ≠ 0 (since a + b ≠ 0 from hypothesis h3)
      have ha : a ≠ 0 := by
        by_contra!
        apply h3
        simp [hb, this]
      simp [hb, ha] at h2
      simp [h2]
      use 0
      simp [Real.sqrt_eq_zero_of_nonpos]
    -- Subcase 1.2: When b ≠ 0
    simp [hb] at h
    use 0
    simp [h, Real.sqrt_eq_zero_of_nonpos]

  -- Case 2: When a + bc = 0
  by_cases h1 : a + b * c = 0
  · simp [h1] at h
    rw [add_comm] at h
    simp at h
    -- Subcase 2.1: When a = 0
    by_cases hb : a = 0
    · -- Prove b ≠ 0 (since a + b ≠ 0 from hypothesis h3)
      have ha : b ≠ 0 := by
        by_contra!
        apply h3
        simp [hb, this]
      simp [hb, ha] at h1
      simp [h1]
      use 0
      simp [Real.sqrt_eq_zero_of_nonpos]
    -- Subcase 2.2: When a ≠ 0
    simp [hb] at h
    use 0
    simp [h, Real.sqrt_eq_zero_of_nonpos]

  -- Case 3: When c + 1 = 0
  by_cases h4 : c + 1 = 0
  · -- If c + 1 = 0, then c = -1
    replace h4 : c = -1 := by linarith
    use 0
    subst c
    simp
  -- Main case: Rearrange the equation to get a * b * (c - 1)² = (a + b)²
  replace h : a * b * (c - 1) ^ 2 = (a + b) ^ 2 := by
    field_simp at h
    linarith
  -- Prove that c-1 ≠ 0, a ≠ 0, and b ≠ 0 by contradiction
  have g1 : c - 1 ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 := by
    refine ⟨?_, ?_, ?_⟩
    all_goals
    by_contra H
    have g1 : a * b * (c - 1) ^ 2 = 0:= by
      rw [H]
      simp
    rw [g1] at h
    replace h : a + b = 0 := by exact pow_eq_zero (id (Eq.symm h))
    trivial
  rcases g1 with ⟨_, g2, g3⟩
  -- Rearrange to isolate (c-1)^2
  replace h : (c - 1) ^ 2 = (a + b) ^ 2 / (a * b) := by
    field_simp at h
    field_simp
    linarith
  -- Prove that (c-3)(c+1) = ((a-b)(c-1)/(a+b))^2
  have g2 : (c - 3) * (c + 1) = (((a - b) * (c - 1)) / (a + b)) ^ 2 := by
    rw [show (c - 3) * (c + 1) = (c - 1) ^ 2 - 4 by ring]
    have g2 : (c - 1) ^ 2 - 4 = (a - b) ^ 2 / (a * b) := by
      rw [h]
      field_simp
      linarith
    rw [g2]
    have g3 : ((a - b) * (c - 1) / (a + b)) ^ 2 =
              (a - b) ^ 2 * (c - 1) ^ 2 / (a + b) ^ 2 := by
      field_simp
      ring
    rw [g3, h]
    field_simp
    ring
  -- Show that (c-3)/(c+1) = ((a-b)(c-1)/((a+b)(c+1)))^2
  have g3 : (c - 3) / (c + 1) =
           ((a - b) * (c - 1) / ((a + b) * (c + 1))) ^ 2 := by
    have g3 : (c - 3) / (c + 1) =
             ((c - 3) * (c + 1)) / (c + 1) ^ 2 := by
      field_simp
      linarith
    rw [g3, g2]
    field_simp
    left
    linarith
  -- Define r and complete the proof using absolute value
  set r := (a - b) * (c - 1) / ((a + b) * (c + 1)) with hr
  clear_value r
  rw [show r ^ 2 = |r| ^ 2 by exact Eq.symm (sq_abs r)] at g3
  rify at g3
  use |r|
  rw [g3]
  rw [show |(↑r : ℝ)| = ↑|r| by norm_cast]
  have hrpos : (↑|r| : ℝ) ≥ 0 := by positivity
  exact Real.sqrt_sq hrpos
