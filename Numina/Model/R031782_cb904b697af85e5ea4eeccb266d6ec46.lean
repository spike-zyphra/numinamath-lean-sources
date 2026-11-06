import Mathlib

theorem algebra_271425 (x y z : ℝ) :
    x^2 + x * y = y^2 + z^2 ∧ z^2 + z * y = y^2 + x^2 ↔
    (x, x, x) = (x, y, z) ∨ (x, 0, x) = (x, y, z) ∨ (x, 0, -x) = (x, y, z) := by
  constructor
  · -- Assume the equations hold, prove the disjunction
    rintro ⟨h1, h2⟩
    have h_sub : (x - z) * (2 * (x + z) + y) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h_sub) with h11 h12
    · -- Case x - z = 0, so z = x
      have hz : z = x := by linarith
      rw [hz] at h1
      have h_eq1 : x * y = y ^ 2 := by
        nlinarith
      have h_eq2 : y * (y - x) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h_eq2) with hy0 hy1
      · -- Case y = 0
        have hy : y = 0 := by linarith
        have h2 : (x, 0, x) = (x, y, z) := by
          simp [hy, hz]
        right
        left
        exact h2
      · -- Case y - x = 0, so y = x
        have hy : y = x := by linarith
        have h1 : (x, x, x) = (x, y, z) := by
          simp [hy, hz]
        left
        exact h1
    · -- Case 2(x + z) + y = 0
      have h_eq1 : y = -2 * (x + z) := by linarith
      rw [h_eq1] at h1
      have h_eq2 : (x + z) ^ 2 = 0 := by
        nlinarith
      have h_eq3 : x + z = 0 := by
        rw [sq_eq_zero_iff] at h_eq2
        linarith
      have hz : z = -x := by linarith
      have hy : y = 0 := by
        rw [hz] at h_eq1
        nlinarith
      have h3 : (x, 0, -x) = (x, y, z) := by
        simp [hy, hz]
      right
      right
      exact h3
  · -- Now prove the reverse direction
    rintro (h | h | h)
    · -- Case (x, x, x) = (x, y, z)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- First equation
        ring
      · -- Second equation
        ring
    · -- Case (x, 0, x) = (x, y, z)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- First equation
        ring
      · -- Second equation
        ring
    · -- Case (x, 0, -x) = (x, y, z)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · -- First equation
        ring
      · -- Second equation
        ring