import Mathlib

theorem algebra_4675 {x y z a b : ℝ} (hxy : x ≠ 0 ∧ y ≠ 0) (hyz : y ≠ 0 ∧ z ≠ 0) (hzx : z ≠ 0 ∧ x ≠ 0)
    (hx : 5 / x = 4 / y) (hy : 4 / y = 6 / z) (h : (a * x + z) / (b * y) = 4) : 5 * a + 6 = 16 * b := by
  rcases hxy with ⟨hxne, hyne⟩
  rcases hyz with ⟨hyne', hzne⟩
  rcases hzx with ⟨hzne', hxne'⟩
  have h1 : 5 * y = 4 * x := by
    field_simp [hxne, hyne] at hx
    linarith
  have h2 : 4 * z = 6 * y := by
    field_simp [hyne, hzne] at hy
    linarith
  have hy_eq : y = 4 / 5 * x := by
    linarith
  have hz_eq : z = 6 / 5 * x := by
    rw [hy_eq] at h2
    linarith
  have eqn : a * x + z = 4 * b * y := by
    have hne : b * y ≠ 0 := by
      have hb : b ≠ 0 := by
        by_contra h0
        rw [h0] at h
        field_simp at h
        all_goals 
          try linarith
          all_goals tauto
      have hy' : y ≠ 0 := hyne
      have : b * y ≠ 0 := mul_ne_zero (show b ≠ 0 by exact hb) (show y ≠ 0 by exact hyne)
      exact this
    field_simp [hne] at h ⊢
    linarith
  rw [hz_eq, hy_eq] at eqn
  have eqn2 : 5 * a * x + 6 * x = 16 * b * x := by
    nlinarith
  have h4 : 5 * a + 6 = 16 * b := by
    apply (mul_left_inj' hxne).mp
    linarith
  linarith