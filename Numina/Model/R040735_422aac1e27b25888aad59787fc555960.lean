import Mathlib

theorem algebra_247779 (d : ℝ) (h₀ : d > 0) :
    {v : ℝ | v > 0 ∧ ∃ t > 0, d / (3 * v) = t ∧ (2 * d) / (3 * v) = t + d / 30} = {10} := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume v ∈ S, prove v = 10
    intro h
    rcases h with ⟨hv, t, ht, h1, h2⟩
    have eq1 : d / (3 * v) = t := by
      linarith
    have eq2 : (2 * d) / (3 * v) = t + d / 30 := by
      linarith
    -- Substitute t from the first equation into the second
    have eq3 : (2 * d) / (3 * v) - (d / (3 * v)) = d / 30 := by
      linarith
    have eq4 : (2 * d) / (3 * v) - (d / (3 * v)) = (d / (3 * v)) := by
      have h33 : (2 * d) / (3 * v) - (d / (3 * v)) = (d / (3 * v)) := by
        field_simp [(show (3 * v) ≠ 0 by
          by_contra h'
          have : v = 0 := by
            nlinarith
            <;> try { nlinarith }
          nlinarith
        ), h₀] at *
        <;> ring_nf <;> nlinarith
        all_goals nlinarith
      nlinarith
    have h14 : d / (3 * v) = d / 30 := by
      linarith [eq3, eq4]
    -- Solve for v
    have h15 : 1 / (3 * v) = 1 / 30 := by
      have h5 : d ≠ 0 := by linarith
      have h6 : d / (3 * v) = d / 30 := h14
      field_simp [(show (3 * v) ≠ 0 by
        by_contra h'
        have : v = 0 := by
          nlinarith
          <;> try { tauto }
          all_goals nlinarith
          all_goals nlinarith
        nlinarith
      ), show (30 : ℝ) ≠ 0 by norm_num, show d ≠ 0 by linarith] at h6 ⊢
      all_goals nlinarith
    have h20 : 3 * v = 30 := by
      field_simp [(show (3 * v) ≠ 0 by
        by_contra h'
        have : v = 0 := by
          nlinarith
          <;> try { tauto }
          all_goals nlinarith
          all_goals nlinarith
        nlinarith
      ), show (30 : ℝ) ≠ 0 by norm_num] at h15 ⊢
      all_goals nlinarith
      all_goals nlinarith
    have h21 : v = 10 := by
      linarith
    linarith
  · -- Assume v = 10, prove v ∈ S
    intro h_eq
    rw [h_eq]
    constructor
    · -- Show 10 > 0
      norm_num
    · -- Show existence of positive time t.
      use (d / 30 : ℝ)
      constructor
      · -- Need to show t > 0.
        have h4 : d / 30 > 0 := by
          apply div_pos
          all_goals linarith
          all_goals try { tauto }
        linarith [h4]
        all_goals nlinarith
      constructor
      · -- First equation: d / (3 * 10) = t
        have h5 : d / (3 * (10 : ℝ)) = (d / 30 : ℝ) := by
          norm_num
          <;> field_simp <;> nlinarith <;> ring_nf
        linarith [h5]
        all_goals nlinarith
        all_goals try { tauto }
      · -- Second equation: (2 * d) / (3 * 10) = t + d / 30
        have h6 : (2 * d) / (3 * (10 : ℝ)) = (d / 30 : ℝ) + d / 30 := by
          field_simp at *
          <;> ring_nf <;> norm_num
        linarith [h6]
        all_goals try { tauto }