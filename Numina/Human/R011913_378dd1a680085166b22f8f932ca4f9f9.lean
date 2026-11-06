import Mathlib

lemma roots_number : ∀ n : ℕ, n > 0 → {z : ℂ| z ^ n = 1}.ncard = n := by
  sorry

theorem algebra_311705 :
    {z : ℂ | z ^ 24 = 1 ∧ ∃ r : ℝ, z ^ 6 = r}.ncard = 12 := by
  have h1 : {z : ℂ | z ^ 24 = 1 ∧ ∃ r : ℝ, z ^ 6 = r} = {z : ℂ | z ^ 12 = 1} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    . rintro ⟨h24, ⟨r, h6⟩⟩

      have h_z_12: z ^ 12 = 1 ∨ z ^ 12 = -1 := by
        rw [(by ring: z ^ 24 = (z ^ 12) ^ 2)] at h24
        rw [sq_eq_one_iff] at h24
        exact h24

      cases' h_z_12 with ha hb
      . assumption
      . have h_z_12_r2: z ^ 12 = r ^ 2 := by
          rw [(by ring: z ^ 12 = (z ^ 6) ^ 2)]
          rw [h6]
        rw [hb] at h_z_12_r2
        norm_cast at h_z_12_r2
        simp at h_z_12_r2
        have h_r_pos: r ^ 2 ≥ 0 := by positivity
        linarith

    . intro h
      constructor
      . rw [(by ring: z^24=(z^12)^2), h]
        norm_num
      . have h_z_6: z ^ 6 = 1 ∨ z ^ 6 = -1 := by
          rw [(by ring: z^12=(z^6)^2)] at h
          rw [sq_eq_one_iff] at h
          exact h
        cases h_z_6
        . use 1
          have:= rootsOfUnity.mkOfPowEq z h

          norm_num
          assumption
        . use -1
          norm_num
          assumption

  rw [h1, roots_number 12 (by norm_num)]
