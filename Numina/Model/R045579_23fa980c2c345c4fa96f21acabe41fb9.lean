import Mathlib

theorem number_theory_176416 (K : ℕ) (hK : K % 7 = 0) (x y z : ℕ)
    (hx : x ≤ 1) (hy : y ≤ 1) (hz : z ≤ 1)  
    (hK1 : K = 0b10110101010101 * 2^6 + x * 2^5 + y * 2^4 + z * 2^3 + 0b110) :
    {(x, y, z)} = ({(0, 1, 0)} : Set (ℕ × ℕ × ℕ)) := by
  have h1 : x = 0 := by
    have eq1 : K % 7 = 0 := hK
    rw [hK1] at eq1
    norm_num [Nat.mul_mod, Nat.add_mod] at eq1
    have h2 : x ≤ 1 := hx
    have h3 : y ≤ 1 := hy
    have h4 : z ≤ 1 := hz
    interval_cases x <;> interval_cases y <;> interval_cases z <;> omega
  have h2 : y = 1 := by
    have eq1 : K % 7 = 0 := hK
    rw [hK1] at eq1
    norm_num [Nat.mul_mod, Nat.add_mod] at eq1
    have h3 : x ≤ 1 := hx
    have h4 : y ≤ 1 := hy
    have h5 : z ≤ 1 := hz
    interval_cases x <;> interval_cases y <;> interval_cases z <;> omega
  have h3 : z = 0 := by 
    have eq1 : K % 7 = 0 := hK
    rw [hK1] at eq1
    norm_num [Nat.mul_mod, Nat.add_mod] at eq1
    have h4 : x ≤ 1 := hx
    have h5 : y ≤ 1 := hy
    have h6 : z ≤ 1 := hz
    interval_cases x <;> interval_cases y <;> interval_cases z <;> omega
  ext ⟨a, b, c⟩
  simp
  constructor
  · -- Assume (x, y, z) = (a, b, c)
    rintro ⟨rfl, rfl, rfl⟩
    simp [h1, h2, h3]
  · -- Assume (a, b, c) = (0, 1, 0)
    rintro ⟨rfl, rfl, rfl⟩
    simp [h1, h2, h3]