import Mathlib.Data.Real.Basic
import Mathlib.Analysis.MeanInequalities

open Real Set
open scoped BigOperators

/-Let $0 \le x,$ $y,$ $z \le 1.$  Find the maximum value of
\[f(x,y,z) = x^2 y + y^2 z + z^2 x - xy^2 - yz^2 - zx^2.\]-/
theorem algebra_21183 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ z ∈ Icc 0 1 ∧
    t = x^2 * y + y^2 * z + z^2 * x - x * y^2 - y * z^2 - z * x^2} (1/4) := by
  unfold IsGreatest
  constructor
  . -- First, we show that 1/4 is in the set
    use 1
    use (1/2)
    use 0
    simp
    ring_nf
    use (by linarith)

  . -- Second, we show that any element in the set is less than or equal to 1/4
    apply mem_upperBounds.mpr
    intro t
    simp
    intro x hx₀ hx₁ y hy₀ hy₁ z hz₀ hz₁ heq
    -- We can factor as follows:
    have h_factor : x^2 * y + y^2 * z + z^2 * x - x * y^2 - y * z^2 - z * x^2 = (x - y) * (x - z) * (y - z) := by
      ring_nf
    rw [h_factor] at heq
    -- The expression has cyclic symmetry, so we can assume x >= y and x >= z
    -- Thus, x - y >= 0 and x - z >= 0
    by_cases hxy : x - y ≥ 0
    · by_cases hxz : x - z ≥ 0
      · by_cases hyz : y < z
        . -- If y < z, then y - z < 0, so the product is <= 0
          have : (x - y) * (x - z) * (y - z) ≤ 0 := by
            have : (y - z) < 0 := by linarith
            apply mul_nonpos_of_nonneg_of_nonpos
            exact Left.mul_nonneg hxy hxz
            linarith
          rw [heq]
          apply le_trans this
          norm_num
        simp at hyz
        -- Then by AM-GM, (x - y)(y - z) <= ((x - y) + (y - z))/2)^2 = (x-z)^2 / 4
        have h_amgm : (x - y) * (y - z) ≤ (x - z)^2 / 4 := by
          have h_pos_xy : 0 ≤ x - y := by linarith
          have h_pos_yz : 0 ≤ y - z := by linarith
          have h_amgm'' : (x-y) * (y-z) ≤ ((x-z)/2)^2 := by
            have : (x - z) = (x-y) + (y-z) := by ring_nf
            rw [this]
            obtain ⟨a, ha⟩ := show ∃a, a = x - y by simp
            obtain ⟨b, hb⟩ := show ∃b, b = y - z by simp
            rw [ha.symm, hb.symm]
            rw [ha.symm] at h_pos_xy
            rw [hb.symm] at h_pos_yz
            have : ((a + b) / 2) ^ 2 = (a^2 + b^2 + 2 * a * b) / 4 := by ring_nf
            rw [this]
            have : 0 ≤ (a^2 + b^2 - 2 * a * b) / 4 := by
              have : (a - b)^2 = a^2 + b^2 - 2 * a * b := by ring_nf
              rw [this.symm]
              positivity
            linarith
          linarith
        have : (x - y) * (y - z) * (x - z) <= (x-z)^3 / 4 := by
          rw [pow_succ, mul_div_right_comm]
          exact mul_le_mul_of_nonneg_right h_amgm hxz
        rw [mul_assoc, mul_comm (y - z), ←mul_assoc] at this
        rw [heq]
        apply le_trans this
        have : x - z ≤ 1 := by linarith
        have : (x - z)^3 ≤ 1 := by exact pow_le_one₀ (by positivity) this
        linarith

      -- y ≤ x < z
      simp at hxz
      have h_amgm : (z - x) * (x - y) ≤ (z - y)^2 / 4 := by
        have h_pos_zx : 0 ≤ z - x := by linarith
        have h_pos_xy : 0 ≤ x - y := by linarith
        have h_amgm'' : (z-x) * (x-y) ≤ ((z-y)/2)^2 := by
          have : (z - y) = (z-x) + (x-y) := by ring_nf
          rw [this]
          obtain ⟨a, ha⟩ := show ∃a, a = z - x by simp
          obtain ⟨b, hb⟩ := show ∃b, b = x - y by simp
          rw [ha.symm, hb.symm]
          rw [ha.symm] at h_pos_zx
          rw [hb.symm] at h_pos_xy
          have : ((a + b) / 2) ^ 2 = (a^2 + b^2 + 2 * a * b) / 4 := by ring_nf
          rw [this]
          have : 0 ≤ (a^2 + b^2 - 2 * a * b) / 4 := by
            have : (a - b)^2 = a^2 + b^2 - 2 * a * b := by ring_nf
            rw [this.symm]
            positivity
          linarith
        linarith
      have hp : (z - x) * (x - y) * (z - y) <= (z-y)^3 / 4 := by
        rw [pow_succ, mul_div_right_comm]
        apply mul_le_mul_of_nonneg_right h_amgm (by linarith)
      have : (z - x) * (x - y) * (z - y) = (x - y) * (x - z) * (y - z) := by ring_nf
      rw [this] at hp
      rw [heq]
      apply le_trans hp
      have : z - y ≤ 1 := by linarith
      have : (z - y)^3 ≤ 1 := by exact pow_le_one₀ (by linarith) this
      linarith


    simp at hxy
    -- x < y
    by_cases hxz : z ≤ x
    · -- x < y and z ≤ x, then z < x < y
      simp at hxz
      -- then (x-y)(x-z)(y-z) <= 0
      have : (x - y) * (x - z) * (y - z) ≤ 0 := by
        rw [mul_comm]
        apply mul_nonpos_of_nonneg_of_nonpos
        linarith
        rw [mul_comm]
        apply mul_nonpos_of_nonneg_of_nonpos
        linarith
        linarith
      rw [heq]
      apply le_trans this
      norm_num
    simp at hxz
    -- x < y and x < z
    by_cases hyz : y < z
    · -- x < y < z
      -- then by AM-GM, (y-x)(z-y) <= (z-x)^2 / 4
      have : (x - y) * (x - z) * (y - z) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos
        apply mul_nonneg_of_nonpos_of_nonpos
        repeat linarith
      rw [heq]
      apply le_trans this
      norm_num
    simp at hyz
    -- x < z < y
    -- then by AM-GM, (z-x)(y-z) <= (y-x)^2 / 4
    have h_amgm : (z - x) * (y - z) ≤ (y - x)^2 / 4 := by
      have h_pos_zx : 0 ≤ z - x := by linarith
      have h_pos_yz : 0 ≤ y - z := by linarith
      have h_amgm'' : (z-x) * (y-z) ≤ ((y-x)/2)^2 := by
        have : (y - x) = (y-z) + (z-x) := by ring_nf
        rw [this]
        obtain ⟨a, ha⟩ := show ∃a, a = y - z by simp
        obtain ⟨b, hb⟩ := show ∃b, b = z - x by simp
        rw [ha.symm, hb.symm]
        rw [ha.symm] at h_pos_yz
        rw [hb.symm] at h_pos_zx
        have : ((a + b) / 2) ^ 2 = (a^2 + b^2 + 2 * a * b) / 4 := by ring_nf
        rw [this]
        have : 0 ≤ (a^2 + b^2 - 2 * a * b) / 4 := by
          have : (a - b)^2 = a^2 + b^2 - 2 * a * b := by ring_nf
          rw [this.symm]
          positivity
        linarith
      linarith
    have h: (z - x) * (y - z) * (y - x) <= (y-x)^3 / 4 := by
      rw [pow_succ, mul_div_right_comm]
      apply mul_le_mul_of_nonneg_right h_amgm (by linarith)
    have : (z - x) * (y - z) * (y - x) = (x - y) * (x - z) * (y - z) := by ring_nf
    rw [this] at h
    rw [heq]
    apply le_trans h
    have : y - x ≤ 1 := by linarith
    have : (y - x)^3 ≤ 1 := by exact pow_le_one₀ (by linarith) this
    linarith
