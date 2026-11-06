import Mathlib

theorem algebra_224561 (m : ℕ) :
    {m |∀ X Y Z: ℝ, (X^m + Y^m + Z^m - (X + Y + Z)^m) % ((Y + Z) * (Z + X) * (X + Y)) = 0} = 
    {m | Odd m} := by 
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Forward: ∀ X Y Z, (X^m + Y^m + Z^m - (X + Y + Z)^m) % ((Y + Z) * (Z + X) * (X + Y)) = 0 → Odd m
    intro h
    have h1 := h 1 (-1 : ℝ) (0 : ℝ)
    norm_num at h1
    have h2 : m % 2 = 1 := by
      by_contra h'
      push_neg at h'
      have h3 : m % 2 = 0 := by 
        omega
      have h4 : ((-1 : ℝ) ) ^ m = 1 := by 
        have h11 : m % 2 = 0 := h3
        have h2 : m = 2 * (m / 2) := by 
          omega
        rw [h2]
        simp [pow_mul, pow_two]
        <;> nlinarith
      nlinarith [ show ((-1 : ℝ) ) ^ m ≥ 0 from by nlinarith [ sq_nonneg ((-1 : ℝ) ^ (m / 2) ) ] ]
    have h3 : Odd m := by 
      exact ⟨m / 2, by omega⟩
    exact h3
  · -- Backward: Odd m → ∀ X Y Z: ℝ, (X^m + Y^m + Z^m - (X + Y + Z)^m) % ((Y + Z) * (Z + X) * (X + Y)) = 0
    intro hm
    have h1 : m % 2 = 1 := by
      obtain ⟨k, hk⟩ := hm
      omega
    intro X Y Z
    by_cases h6 : (Y + Z) * (Z + X) * (X + Y) = 0 
    · -- When divisor is 0, need polynomial to be zero
      have h7 : X^m + Y^m + Z^m - (X + Y + Z)^m = 0 := by
        have h8 : (Y + Z) * (Z + X) * (X + Y) = 0 := h6
        cases' (mul_eq_zero.mp h8) with h8 h8
        cases' (mul_eq_zero.mp h8) with h8 h8
        · -- y + z = 0
          have h9 : Y = -Z := by linarith
          rw [show Y = -Z by linarith]
          have h9' : (-Z)^m = - (Z^m) := by 
            have h5 : m % 2 = 1 := h1
            have h7 : (-Z)^m = (-1)^m * (Z)^m := by ring_nf
            have h8 : (-1 : ℝ)^m = -1 := by 
              have h5' : m % 2 = 1 := h5
              have h10 : (-1 : ℝ)^m = -1 := by
                have h9 : m % 2 = 1 := h5'
                have h14 : m = 2 * (m / 2) + 1 := by omega
                rw [h14]
                simp [pow_add, pow_mul]
                <;> ring_nf <;> norm_num
              assumption
            rw [h7, h8]
            <;> ring_nf <;> norm_num
          simp [h9']
          <;> ring_nf <;> norm_num
          all_goals linarith 
        · -- z + x = 0
          have h9 : Z = -X := by linarith
          rw [show Z = -X by linarith]
          have h9' : (-X)^m = - (X^m) := by 
            have h5 : m % 2 = 1 := h1
            have h7 : (-X)^m = (-1)^m * (X)^m := by ring_nf
            have h8 : (-1 : ℝ)^m = -1 := by 
              have h5' : m % 2 = 1 := h5
              have h10 : (-1 : ℝ)^m = -1 := by
                have h9 : m % 2 = 1 := h5'
                have h14 : m = 2 * (m / 2) + 1 := by omega
                rw [h14]
                simp [pow_add, pow_mul]
                all_goals ring_nf <;> norm_num
              assumption
            rw [h7, h8]
            all_goals ring_nf <;> norm_num
          simp [h9']
          <;> ring_nf <;> norm_num
          all_goals linarith 
        · -- x + y = 0
          have h9 : X = -Y := by linarith
          rw [show X = -Y by linarith]
          have h9' : (-Y)^m = - (Y^m) := by 
            have h5 : m % 2 = 1 := h1
            have h7 : (-Y)^m = (-1)^m * (Y)^m := by ring_nf
            have h8 : (-1 : ℝ)^m = -1 := by 
              have h5' : m % 2 = 1 := h5
              have h10 : (-1 : ℝ)^m = -1 := by
                have h9 : m % 2 = 1 := h5'
                have h14 : m = 2 * (m / 2) + 1 := by omega
                rw [h14]
                simp [pow_add, pow_mul]
                all_goals ring_nf <;> norm_num
              assumption
            rw [h7, h8]
            all_goals ring_nf <;> norm_num
          simp [h9']
          <;> ring_nf <;> norm_num
          all_goals linarith 
      simp [h7, h6]
      <;> ring_nf <;> norm_num
      all_goals tauto
    · -- The divisor is not zero
      simp [show (Y + Z) * (Z + X) * (X + Y) ≠ 0 by exact h6]
      <;> ring_nf <;> norm_num 
      all_goals tauto