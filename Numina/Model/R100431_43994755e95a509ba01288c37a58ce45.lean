import Mathlib

theorem algebra_111760 (a b c : ℤ) :
    Even ((7 * a + b - 2 * c + 1) * (3 * a - 5 * b + 4 * c + 10)) := by
  have h4 : ((7 * a + b - 2 * c + 1) * (3 * a - 5 * b + 4 * c + 10)) % 2 = 0 := by
    have eq1 : (7 * a + b - 2 * c + 1) % 2 = (a + b + 1) % 2 := by
      omega
    have eq2 : (3 * a - 5 * b + 4 * c + 10) % 2 = (a + b) % 2 := by
      omega
    have eq3 : ((7 * a + b - 2 * c + 1) * (3 * a - 5 * b + 4 * c + 10)) % 2 =
      (((7 * a + b - 2 * c + 1) % 2) * ((3 * a - 5 * b + 4 * c + 10) % 2)) % 2 := by
      simp [Int.mul_emod]
    rw [eq3]
    rw [eq1, eq2]
    have h5 : (( (a + b + 1) % 2 ) * ( (a + b) % 2 ) ) % 2 = 0 := by
      have h1 : a % 2 = 0 ∨ a % 2 = 1 := by
        omega
      have h2 : b % 2 = 0 ∨ b % 2 = 1 := by
        omega
      rcases h1 with (ha | ha)
      <;> rcases h2 with (hb | hb)
      <;> simp [Int.add_emod, Int.mul_emod, ha, hb] <;> omega
    omega
  exact ⟨(7 * a + b - 2 * c + 1) * (3 * a - 5 * b + 4 * c + 10) / 2, by
    omega⟩