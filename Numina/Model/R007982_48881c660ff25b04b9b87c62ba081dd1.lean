import Mathlib
theorem algebra_96708
: IsGreatest {t | ∃ a b c:ℕ, ∃ x y:ℝ, a≠b ∧ b≠c ∧ c≠a ∧ a ∈ Set.Icc 0 9 ∧
b ∈ Set.Icc 0 9 ∧ c ∈ Set.Icc 0 9 ∧ x ≠ y ∧ (x-a)*(x-b)+(x-b)*(x-c)=0 ∧ (y-a)*(y-b)+(y-b)*(y-c)=0 ∧
t = x+y} 16.5 := by
  constructor
  · -- first part, exists some case t = 16.5
    use 8, 9, 7
    use 9, 7.5
    constructor
    · norm_num -- a≠b
    constructor
    · norm_num -- b≠c
    constructor
    · norm_num -- c≠a
    constructor
    · norm_num [Set.mem_Icc] -- a ∈ Set.Icc 0 9
    constructor
    · norm_num [Set.mem_Icc] -- b ∈ Set.Icc 0 9
    constructor
    · norm_num [Set.mem_Icc] -- c ∈ Set.Icc 0 9
    constructor
    · norm_num -- x ≠ y
    constructor
    · norm_num -- (x-a)*(x-b)+(x-b)*(x-c)=0
    constructor
    · norm_num -- (y-a)*(y-b)+(y-b)*(y-c)=0
    · norm_num -- t = x+y
  · -- second part, for all t in the set, t ≤ 16.5
    intro t ht
    rcases ht with ⟨a, b, c, x, y, h1, h2, h3, ha, hb, hc, h4, h5, h6, ht⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    have h9 : x + y = (a + 2 * b + c) / 2 := by
      have eq1 : 2 * x^2 - (a + 2 * b + c) * x + (a * b + b * c) = 0 := by
        nlinarith
      have eq2 : 2 * y^2 - (a + 2 * b + c) * y + (a * b + b * c) = 0 := by
        nlinarith
      have eq3 : 2 * (x^2 - y^2) - (a + 2 * b + c) * (x - y) = 0 := by
        nlinarith [eq1, eq2]
      have h10 : 2 * (x + y) - (a + 2 * b + c) = 0 := by
        apply (mul_left_inj' (sub_ne_zero.mpr h4)).mp
        linarith
      linarith
    have h17 : (a : ℝ) + 2 * (b : ℝ) + (c : ℝ) ≤ 33 := by
      have h17 : a + 2 * b + c ≤ 33 := by
        by_cases h : b < 9
        · -- b < 9, so max b is 8
          omega
        · -- b = 9
          have h21 : b = 9 := by omega
          rw [h21] at *
          omega
      exact_mod_cast h17
    nlinarith [ht, h9, h17]