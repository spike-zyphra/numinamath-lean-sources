import Mathlib

theorem algebra_99601 (b : ℝ) :
    (∀ m : ℝ, ∃ x y : ℝ, x^2 + 2 * y^2 = 3 ∧ y = m * x + b) ↔
    b ∈ Set.Icc (-Real.sqrt 6 / 2) (Real.sqrt 6 / 2) := by
  constructor
  · -- Assume that for all $m \in \mathbb{R}$, there exists $(x, y)$ such that $x^2 + 2y^2 = 3$ and $y = mx + b$. Prove $b \in \left[ -\frac{\sqrt{6}}{2}, \frac{\sqrt{6}}{2} \right]$.
    intro h
    constructor
    · -- Show that $-Real.sqrt 6 / 2 \leq b$
      by_contra h1
      push_neg at h1
      have h2 := h 0
      rcases h2 with ⟨x, y, hxy, hy⟩
      have h3 : y = b := by
        linarith
      rw [h3] at hxy
      have h4 : x ^ 2 ≥ 0 := by nlinarith
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (b), sq_nonneg (b + Real.sqrt 6 / 2), sq_nonneg (b - Real.sqrt 6 / 2)]
    · -- Show that $b \leq Real.sqrt 6 / 2$
      by_contra h2
      push_neg at h2
      have h2 := h 0
      rcases h2 with ⟨x, y, hxy, hy⟩
      have h3 : y = b := by
        linarith
      rw [h3] at hxy
      have h4 : x ^ 2 ≥ 0 := by nlinarith
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (b), sq_nonneg (b + Real.sqrt 6 / 2), sq_nonneg (b - Real.sqrt 6 / 2)]
  · -- Show the converse: if $b \in \left[ -\frac{\sqrt{6}}{2}, \frac{\sqrt{6}}{2} \right]$, then for all $m \in \mathbb{R}$, there exists $(x, y) \in M \cap N$.
    rintro ⟨hb1, hb2⟩
    intro m
    have h1 : (4 * m * b) ^ 2 - 4 * (1 + 2 * m ^ 2) * (2 * b ^ 2 - 3) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (b), sq_nonneg (b + Real.sqrt 6 / 2), sq_nonneg (b - Real.sqrt 6 / 2)]
    have h2 : ∃ x, (1 + 2 * m ^ 2) * x ^ 2 + 4 * m * b * x + (2 * b ^ 2 - 3) = 0 := by
      have h1' : (4 * m * b) ^ 2 - 4 * (1 + 2 * m ^ 2) * (2 * b ^ 2 - 3) ≥ 0 := h1
      use (-4 * m * b + Real.sqrt ((4 * m * b) ^ 2 - 4 * (1 + 2 * m ^ 2) * (2 * b ^ 2 - 3)) ) / (2 * (1 + 2 * m ^ 2))
      field_simp
      ring_nf
      rw [Real.sq_sqrt (by linarith)]
      <;> nlinarith
    rcases h2 with ⟨x, hx⟩
    use x
    use (m * x + b)
    constructor
    · -- Show that $x^2 + 2y^2 = 3$
      nlinarith [hx]
    · -- Show that $y = m * x + b$
      all_goals ring