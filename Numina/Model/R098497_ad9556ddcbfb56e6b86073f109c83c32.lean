import Mathlib

theorem algebra_277686 {x y : ℤ} (hy : y ≠ 0) (hxy : x = y + 2016) (hq : x / y = 15) (hrem : x % y = 0) :
    x = 2160 := by
  have h1 : x = 15 * y := by
    rw [← Int.ediv_add_emod x y, hq, hrem]
    all_goals ring_nf
    all_goals omega
  rw [hxy] at h1
  have hy_eq : y = 144 := by
    omega
  rw [hy_eq] at hxy
  omega