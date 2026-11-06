import Mathlib

theorem algebra_301684 (a : ℝ) (ha : -2 ≤ a) (B C : Set ℝ)
    (hB : B = {y | ∃ x ∈ Set.Icc (-2) a, y = 2 * x + 3})
    (hC : C = {z | ∃ x ∈ Set.Icc (-2) a, z = x ^ 2}) :
    C ⊆ B ↔ 1 / 2 ≤ a ∧ a ≤ 3 := by
  constructor
  · -- Prove the forward direction: If $C \subseteq B$, then $1/2 \leq a \wedge a \leq 3$
    intro h
    have h1 : 1 / 2 ≤ a := by
      have h2 : (4 : ℝ) ∈ C := by
        rw [hC]
        use -2
        constructor
        · -- Show that -2 ∈ Icc (-2) a
          exact ⟨by linarith, by linarith⟩
        · -- Show that 4 = (-2) ^ 2
          norm_num
      have h3 : (4 : ℝ) ∈ B := h h2
      rw [hB] at h3
      rcases h3 with ⟨x, hx, hx2⟩
      have hx1 : -2 ≤ x := by
        have h1 : x ∈ Set.Icc (-2 : ℝ) a := hx
        exact h1.1
      have hx2a : x ≤ a := by
        have h1 : x ∈ Set.Icc (-2 : ℝ) a := hx
        exact h1.2
      have h5 : 2 * x + 3 = (4 : ℝ) := by linarith
      have hx3 : x = (1 / 2 : ℝ) := by linarith
      linarith
    have h2 : a ≤ (3 : ℝ) := by
      have h2 : a ^ 2 ∈ C := by
        rw [hC]
        use a
        constructor
        · -- Show that a ∈ Icc (-2) a
          exact ⟨by linarith, by linarith⟩
        · -- Show that a ^ 2 = a ^ 2
          all_goals norm_num
      have h4 : a ^ 2 ∈ B := h h2
      rw [hB] at h4
      rcases h4 with ⟨y, hy, hy2⟩
      have hy1 : -2 ≤ y := by
        have h1 : y ∈ Set.Icc (-2 : ℝ) a := hy
        exact h1.1
      have hy2a : y ≤ a := by
        have h1 : y ∈ Set.Icc (-2 : ℝ) a := hy
        exact h1.2
      have h7 : 2 * y + 3 = a ^ 2 := by linarith
      nlinarith
    constructor
    · linarith
    · linarith
  · -- Prove the reverse direction: If $1/2 \leq a \wedge a \leq 3$, then $C \subseteq B$
    rintro ⟨ha1, ha2⟩
    intro z hz
    have h4 : z ∈ C := hz
    rw [hC] at h4
    rcases h4 with ⟨x, hx, hz⟩
    have hx1 : -2 ≤ x := by
      have h1 : x ∈ Set.Icc (-2 : ℝ) a := hx
      exact h1.1
    have hx2 : x ≤ a := by
      have h1 : x ∈ Set.Icc (-2 : ℝ) a := hx
      exact h1.2
    have h5 : z ∈ B := by
      rw [hB]
      use (z - 3) / 2
      constructor
      · -- Show that (z - 3) / 2 ∈ Icc (-2) a
        constructor
        · -- Show that -2 ≤ (z - 3) / 2
          nlinarith [sq_nonneg x, sq_nonneg (x - a), sq_nonneg (x + 2)]
        · -- Show that (z - 3) / 2 ≤ a
          nlinarith [sq_nonneg x, sq_nonneg (x - a), sq_nonneg (x + 2)]
      · -- Show that z = 2 * ((z - 3) / 2) + 3
        linarith
    exact h5
  all_goals try linarith