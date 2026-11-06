import Mathlib

theorem number_theory_228958 :
    {(a, b) : ℕ × ℕ | a + b = 316 ∧ Nat.lcm a b = 4560} = {(240, 76), (76, 240)} := by
  ext ⟨a, b⟩
  simp
  constructor
  · -- First, if (a, b) satisfies a + b = 316 and lcm(a, b) = 4560, then (a, b) is in {(240, 76), (76, 240)}.
    rintro ⟨ha1, ha2⟩
    have h2 : b = 316 - a := by
      omega
    rw [h2] at ha2
    have h1 : a ≤ 316 := by
      omega
    interval_cases a <;> norm_num [Nat.lcm] at ha2 ⊢
    <;> omega
  · -- Second, (240, 76) and (76, 240) satisfy a + b = 316 and lcm(a, b) = 4560.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- First pair (240, 76)
      constructor <;> norm_num [Nat.lcm]
    · -- Second pair (76, 240)
      constructor <;> norm_num [Nat.lcm]