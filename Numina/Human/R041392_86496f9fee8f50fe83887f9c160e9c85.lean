import Mathlib

theorem algebra_88526 : IsLeast {w : ℤ | ∃ (x y z : ℤ), 0 < x ∧ 0 < y ∧ 0 < z ∧ x * y + z = 160 ∧ w = x + y * z} 50 := by
  constructor
  {
    use 26, 6, 4
    norm_num
  }
  rintro w ⟨x, y, z, hx, hy, hz, h, rfl⟩
  have hzeq : z = 160 - x * y := by linarith only [h]
  have hxy : x * y ≤ 159 := by linarith only [h, hz]
  have hx₂ : x ≤ 159 / y := Int.le_ediv_of_mul_le hy hxy
  have hy₀ : y ≤ 159 := by nlinarith only [hx, hxy]
  subst hzeq
  suffices H : ∀ y ∈ Finset.Ioc (0 : ℤ) 159, ∀ x ∈ Finset.Ioc (0 : ℤ) (159 / y), 50 ≤ x + y * (160 - x * y) from H y (Finset.mem_Ioc.mpr ⟨hy, hy₀⟩) x (Finset.mem_Ioc.mpr ⟨hx, hx₂⟩)
  native_decide
