import Mathlib

theorem number_theory_3441 (x y : ℤ) : ¬(6*x-1=y^2) := by
  intro h
  have h1 : y^2 % 3 = 0 ∨ y^2 % 3 = 1 := by
    have h1 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by
      omega
    rcases h1 with (h1 | h1 | h1)
    · -- y ≡ 0 mod 3, so y² ≡ 0
      simp [pow_two, Int.mul_emod, h1]
    · -- y ≡ 1 mod 3, so y² ≡ 1
      simp [pow_two, Int.mul_emod, h1]
    · -- y ≡ 2 mod 3, so y² ≡ 4 ≡ 1
      simp [pow_two, Int.mul_emod, h1]
  have h2 : y^2 % 3 = 2 := by 
    omega
  rcases h1 with (h1 | h1)
  · -- $y^2 \equiv 0 \pmod{3}$ contradicts $y^2 \equiv 2 \pmod{3}$
    omega
  · -- $y^2 \equiv 1 \pmod{3}$ contradicts $y^2 \equiv 2 \pmod{3}$
    omega