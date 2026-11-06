import Mathlib

theorem number_theory_6551 (z : ℝ) (hz : IsGreatest {z : ℝ | 0 < z ∧ ⌊(3 / z)⌋ + ⌊(4 / z)⌋ = 5} z) :
    21 * z = (28 : ℝ) := by
  have h1 : z ∈ {z : ℝ | 0 < z ∧ ⌊(3 / z)⌋ + ⌊(4 / z)⌋ = 5} := hz.left
  have h2 : ∀ x : ℝ, x ∈ {z : ℝ | 0 < z ∧ ⌊(3 / z)⌋ + ⌊(4 / z)⌋ = 5} → x ≤ z := hz.right
  rcases h1 with ⟨hz_pos, heq⟩

  have h5 : z ≤ (4 / 3 : ℝ) := by
    by_contra h
    push_neg at h
    have h6 : ⌊(3 / z)⌋ + ⌊(4 / z)⌋ < (5 : ℤ) := by 
      have h6 : ⌊(3 / z)⌋ ≤ 2 := by
        have h7 : 3 / z < (3 : ℝ) := by 
          have h11 : z > (4 / 3 : ℝ) := by linarith
          have h9 : 3 / z < (3 : ℝ) := by
            have h11 : z > (1 : ℝ) := by nlinarith
            have h12 : z > (0 : ℝ) := by nlinarith
            apply (div_lt_iff₀ (by linarith)).mpr
            nlinarith
          linarith
        have h10 : ⌊(3 / z : ℝ)⌋ ≤ 2 := by
          by_contra h
          push_neg at h
          have h13 : (3 / z : ℝ) ≥ (3 : ℝ) := by
            have h14 : ⌊(3 / z : ℝ)⌋ ≥ (3 : ℤ) := by linarith
            have h15 : (3 / z : ℝ) ≥ (⌊(3 / z : ℝ)⌋ : ℝ) := by exact Int.floor_le (3 / z)
            have h16 : (⌊(3 / z : ℝ)⌋ : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h14
            nlinarith
          linarith
        exact_mod_cast h10

      have h7 : ⌊(4 / z)⌋ ≤ 2 := by
        have h7 : 4 / z < (3 : ℝ) := by
          have h11 : z > (4 / 3 : ℝ) := by linarith
          have h11 : z > (1 : ℝ) := by nlinarith
          -- For z > 4/3, 4/z < 3
          have h12 : z > (0 : ℝ) := by nlinarith
          apply (div_lt_iff₀ (by linarith)).mpr
          nlinarith
        -- Since 4/z < 3, floor is at most 2
        have h10 : ⌊(4 / z : ℝ)⌋ ≤ 2 := by 
          by_contra h
          push_neg at h
          have h13 : (4 / z : ℝ) ≥ (3 : ℝ) := by
            have h14 : ⌊(4 / z : ℝ)⌋ ≥ (3 : ℤ) := by linarith
            have h15 : (4 / z : ℝ) ≥ (⌊(4 / z : ℝ)⌋ : ℝ) := by exact Int.floor_le (4 / z)
            have h16 : (⌊(4 / z : ℝ)⌋ : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h14
            nlinarith
          linarith
        exact_mod_cast h10

      omega
    omega

  have h8 : z ≤ (4 / 3 : ℝ) := h5

  -- Show that z ≥ 4/3
  have h9 : (4 / 3 : ℝ) ∈ {z : ℝ | 0 < z ∧ ⌊(3 / z)⌋ + ⌊(4 / z)⌋ = 5} := by 
    constructor 
    · norm_num 
    · norm_num 
  -- maximality of z
  have h10 : (4 / 3 : ℝ) ≤ z := by 
    apply h2 (4 / 3) h9 
  -- contradiction 
  nlinarith