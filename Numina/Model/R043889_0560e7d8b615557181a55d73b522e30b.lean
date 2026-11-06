import Mathlib

open BigOperators Real

theorem number_theory_78747 :
  ∃ n : ℕ, 4 ≤ n ∧ ∀ m ∈ Set.Ioo (2 * n / 3) n, ∃ k : ℕ,
    2 ≤ k ∧ k ≤ 2022 ∧ ∃ x : ℚ, x > 0 ∧ x < (n - m) / m ∧
      (Nat.floor (x * (-k : ℤ))) % k = 0 := by
  use 4
  constructor
  · norm_num -- proves 4 ≤ 4
  · intro m hm
    rcases Set.mem_Ioo.mp hm with ⟨h1, h2⟩
    have h3 : m = 3 := by
      omega
    rw [h3] at *
    use 2
    constructor
    · norm_num -- proves 2 ≤ 2
    constructor
    · norm_num -- proves 2 ≤ 2022
    use (1 / 4 : ℚ)
    native_decide