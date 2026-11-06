import Mathlib

theorem algebra_213224 :
    {(t, x, y, z) : ℝ × ℝ × ℝ × ℝ | t * (x + y + z) = 0 ∧ t * (x + y) + z = 1 ∧ t * x + y + z = 2} =
    {(0, x, 1, 1) | x : ℝ} ∪ 
    {p | ∃ (t : ℝ), t ≠ 0 ∧ t ≠ 1 ∧ p = (t, 2 / (t - 1), -1 / (t - 1), -1 / (t - 1))} := by
  ext ⟨t, x, y, z⟩
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · -- Forward: from system of equations to cases 
    rintro ⟨h1, h2, h3⟩
    by_cases ht0 : t = 0 
    · -- Case t = 0 
      have hz : z = 1 := by 
        rw [ht0] at h2 
        linarith 
      have hy : y = 1 := by 
        rw [ht0] at h3 
        linarith [hz] 
      left 
      simp [ht0, hy, hz]
      <;> try { tauto } 
    · -- Case t ≠ 0 
      have ht_n0 : t ≠ 0 := by 
        intro h 
        apply ht0 
        linarith 
      have h_eq1 : x + y + z = 0 := by 
        apply (mul_right_inj' ht_n0).mp 
        linarith [h1] 
      have ht1_eq : z = -x - y := by 
        linarith [h_eq1] 
      have h_eq3 : (t - 1) * x = 2 := by 
        rw [ht1_eq] at h3 
        nlinarith 
      have h_eq4 : (t - 1) * (x + y) = 1 := by 
        rw [ht1_eq] at h2 
        nlinarith 
      by_cases ht1' : t = 1 
      · -- Case t = 1: Show inconsistency 
        rw [ht1'] at h_eq3 
        linarith 
      · -- Case t ≠ 1 
        have ht_n1 : t ≠ 1 := by 
          intro h 
          apply ht1' 
          linarith 
        have htne0 : t - 1 ≠ 0 := by 
          intro h' 
          have : t = 1 := by 
            linarith 
          contradiction 
        have ht2_eq1 : x = 2 / (t - 1) := by 
          have htne0' : t - 1 ≠ 0 := htne0 
          field_simp [htne0']
          <;> nlinarith [h_eq3] 
        have ht2_eq2 : y = -1 / (t - 1) := by 
          have h_eq5 : x + y = 1 / (t - 1) := by 
            have htne0' : t - 1 ≠ 0 := htne0 
            have eq4' : (t - 1) * (x + y) = 1 := h_eq4 
            field_simp [htne0'] at eq4' ⊢
            <;> nlinarith 
          rw [ht2_eq1] at h_eq5 
          have htne0' : t - 1 ≠ 0 := htne0 
          field_simp [htne0'] at h_eq5 ⊢ 
          <;> nlinarith 
        have ht2_eq3 : z = -1 / (t - 1) := by 
          rw [ht1_eq]
          rw [ht2_eq1, ht2_eq2]
          have htne0' : t - 1 ≠ 0 := htne0 
          field_simp [htne0']
          <;> ring 
        right 
        refine' ⟨t, ht_n0, ht_n1, ?_⟩ 
        ext 
        · -- First element (t)
          simp 
        · -- Second element (x)
          simp [ht2_eq1]
        · -- Third element (y)
          simp [ht2_eq2]
        · -- Fourth  element (z)
          simp [ht2_eq3]
  · -- Backward: from cases to system of equations 
    rintro (h | h)
    · -- Case h ∈ left side 
      rcases h with ⟨x, he⟩ 
      have ht0 : t = 0 := by 
        simp [Prod.ext_iff] at he 
        try tauto 
      have hy1 : y = 1 := by 
        simp [Prod.ext_iff] at he 
        try tauto 
      have hz1 : z = 1 := by 
        simp [Prod.ext_iff] at he 
        try tauto 
      constructor 
      · -- Show t * (x + y + z) = 0 
        rw [ht0]
        linarith 
      constructor 
      · -- Show t * (x + y) + z = 1 
        rw [ht0]
        linarith [hz1] 
      · -- Show t * x + y + z = 2 
        rw [ht0]
        linarith [hy1, hz1] 
    · -- Case h ∈ right side 
      rcases h with ⟨t₀, ht₀0, ht₀1, he⟩ 
      have ht_eq : t = t₀ := by 
        simp [Prod.ext_iff] at he 
        try tauto 
      have hx_eq : x = 2 / (t₀ - 1) := by 
        simp [Prod.ext_iff] at he 
        try tauto 
      have hy_eq : y = -1 / (t₀ - 1) := by 
        simp [Prod.ext_iff] at he 
        try tauto 
      have hz_eq : z = -1 / (t₀ - 1) := by 
        simp [Prod.ext_iff] at he 
        try tauto 
      rw [ht_eq, hx_eq, hy_eq, hz_eq] 
      constructor 
      · -- Show t₀ * (x₀ + y₀ + z₀) = 0 
        have htne0 : t₀ - 1 ≠ 0 := by 
          intro h'
          apply ht₀1 
          linarith 
        field_simp [htne0] 
        <;> nlinarith 
      constructor 
      · -- Show t₀ * (x₀ + y₀) + z₀ = 1 
        have htne0 : t₀ - 1 ≠ 0 := by 
          intro h'
          apply ht₀1 
          linarith 
        field_simp [htne0] 
        <;> nlinarith 
      · -- Show t₀ * x₀ + y₀ + z₀ = 2 
        have htne0 : t₀ - 1 ≠ 0 := by 
          intro h'
          apply ht₀1 
          linarith 
        field_simp [htne0] 
        <;> nlinarith