import Mathlib

open Set Real

theorem algebra_298994 {a : ℝ} (ha : |a| ≤ 1) :
    {x | ∃ y : ℝ, x^2 + 9 * y^2 = 9} ∩ {x | ∃ y : ℝ, x^2 + y^2 - 2 * a * x = 0} =
    {x | a - |a| ≤ x ∧ x ≤ a + |a|} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter]
  constructor
  · -- Assume $x \in M \cap N$, so both conditions hold.
    rintro ⟨⟨y1, h1⟩, ⟨y2, h2⟩⟩
    have h3 : x ^ 2 ≤ 9 := by
      nlinarith [sq_nonneg y1]
    have h4 : (x - a) ^ 2 ≤ a ^ 2 := by
      have hy2 : y2 ^ 2 ≥ 0 := sq_nonneg y2
      nlinarith
    constructor
    · -- Show $a - |a| ≤ x$
      cases' abs_cases a with ha1 ha1
      · -- If a ≥ 0, then |a| = a, so a - a ≤ x
        nlinarith [sq_nonneg (x - a)]
      · -- If a < 0, then |a| = -a, so a - (-a) ≤ x
        nlinarith [sq_nonneg (x - a)]
    · -- Show x ≤ a + |a|
      cases' abs_cases a with ha1 ha1
      · -- If a ≥ 0, then |a| = a, so x ≤ a + a
        nlinarith [sq_nonneg (x - a)]
      · -- If a < 0, then |a| = -a, so x ≤ a + (-a)
        nlinarith [sq_nonneg (x - a)]
  · -- Assume $x \in \{x \mid a - |a| \leq x \land x \leq a + |a|\}$
    rintro ⟨h1, h2⟩
    constructor
    · -- Show existence in M.
      have h3 : x ^ 2 ≤ 9 := by
        cases' abs_cases a with ha1 ha1
        · -- If a ≥ 0, then a ≤ 1
          nlinarith [abs_le.mp ha, h1, h2]
        · -- If a < 0, then a ≥ -1
          nlinarith [abs_le.mp ha, h1, h2]
      use Real.sqrt ((9 - x^2) / 9)
      have h4 : (9 - x^2) / (9 : ℝ) ≥ 0 := by
        linarith
      have h5 : (Real.sqrt ((9 - x^2) / 9) : ℝ) ^ 2 = (9 - x^2) / 9 := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith
    · -- Show existence in N.
      have h6 : (x - a) ^ 2 ≤ a ^ 2 := by
        cases' abs_cases a with ha1 ha1
        · -- If a ≥ 0, then |a| = a
          nlinarith [abs_le.mp ha, h1, h2]
        · -- If a < 0, then |a| = -a
          nlinarith [abs_le.mp ha, h1, h2]
      use Real.sqrt (a^2 - (x - a)^2)
      have h7 : a^2 - (x - a)^2 ≥ 0 := by
        linarith [h6]
      have h8 : (Real.sqrt (a^2 - (x - a)^2) : ℝ) ^ 2 = a^2 - (x - a)^2 := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith