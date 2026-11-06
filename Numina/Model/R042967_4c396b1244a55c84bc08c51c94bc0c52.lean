import Mathlib

theorem algebra_290553 :
  {(a, b, c) : ℤ × ℤ × ℤ | 
    a > 0 ∧ b > 0 ∧ c > 0 ∧
    a = 3 * (a / 3) ∧ b = 4 * (b / 4) ∧ c = 5 * (c / 5) ∧
    (∃ x y z : ℤ, x > 0 ∧ y > 0 ∧ z > 0 ∧ a = 3 * x ∧ b = 4 * y ∧ c = 5 * z ∧
    2 * x + z = 3 * y + x ∧
    3 * y + x = 4 * z + y)} =
  {(6 * k, 4 * k, 5 * k) | k > (0 : ℤ) } := by
  ext ⟨a, b, c⟩ 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · -- Assume (a, b, c) in the left side, prove in the right side
    rintro ⟨ha, hb, hc, ha3, hb4, hc5, ⟨x, y, z, hx, hy, hz, ha1, hb1, hc1, h1, h2⟩⟩

    have h3 : x + z = 3 * y := by
      omega

    have h4 : x + 2 * y = 4 * z := by 
      omega

    have h5 : x = 2 * y := by 
      omega

    have h6 : z = y := by 
      omega

    use y 
    constructor
    · -- Show k > 0 
      omega
    all_goals
      simp [show a = 6 * y by omega, show b = 4 * y by omega, show c = 5 * y by omega] 
      <;> omega
  · -- Assume (6k, 4k, 5k) in the right side, prove in the left side
    rintro ⟨k, hk, ⟨rfl, rfl, rfl⟩⟩ 
    constructor
    · -- Show a > 0 
      omega 
    constructor 
    · -- Show b > 0 
      omega 
    constructor 
    · -- Show c > 0 
      omega 
    constructor 
    · -- Show a = 3 * (a / 3)
      omega 
    constructor 
    · -- Show b = 4 * (b / 4)
      omega 
    constructor 
    · -- Show c = 5 * (c / 5)
      omega 
    · -- Show the existence of x y z 
      use 2 * k, k, k 
      constructor 
      · -- Show x > 0 
        omega 
      constructor 
      · -- Show y > 0 
        omega 
      constructor 
      · -- Show z > 0 
        omega 
      constructor 
      · -- Show a = 3 * x 
        omega 
      constructor 
      · -- Show b = 4 * y 
        omega 
      constructor 
      · -- Show c = 5 * z 
        omega 
      constructor 
      · -- Show 2 * x + z = 3 * y + x 
        omega 
      · -- Show 3 * y + x = 4 * z + y 
        omega