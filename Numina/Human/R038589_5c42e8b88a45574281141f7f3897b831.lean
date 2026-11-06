import Mathlib

/-Let $d$ be a positive number such that when $109$ is divided by $d$, the remainder is $4.$ Compute the sum of all possible two-digit values of $d$.-/
theorem algebra_17080 {r : Set ℕ} (hr : r = {d | d ≥ 10 ∧ d < 100 ∧ 109 ≡ 4 [MOD d]}) :
    (r = {15, 21, 35}) ∧ ∑d∈ {15, 21, 35}, d = 71 := by
  constructor
  . -- r = {15, 21, 35}
    ext d
    rw [hr]
    constructor
    . -- d ∈ r -> d ∈ {15, 21, 35}
      -- intro and rcases d ≥ 10 ∧ d < 100 ∧ 109 % d = 4
      -- to hd₁: d ≥ 10, hd₂: d < 100, hp: 109 % d = 4
      rintro ⟨hd₁, ⟨hd₂, hp⟩⟩
      -- Then each of the two-digit numbers that will divide 109 with a remainder of 4 will divide 105 exactly
      -- hp: d ∣ 105
      rw [Nat.modEq_iff_dvd] at hp
      simp at hp
      norm_cast at hp
      -- Since the prime factors of 105 are 3, 5, and 7
      -- so, the prime factors of d must be a subset of {3, 5, 7}
      have : Nat.divisors 105 = {1, 3, 5, 7, 15, 21, 35, 105} := by rfl
      -- we have: d ∈ {1, 3, 5, 7, 15, 21, 35, 105} because d ∣ 105
      have hd: d ∈ Nat.divisors 105 := by
        rw [Nat.mem_divisors]
        simp
        exact hp
      rw [this] at hd

      -- Although this may seem complicated, the answer actually implicitly contains the idea of enumerating all the possibilities.
      by_cases hd₁: d = 15
      . -- d = 3 * 5 = 15
        apply Or.inl hd₁
      by_cases hd₂: d = 21
      . -- d = 3 * 7 = 21
        apply Or.inr (Or.inl hd₂)
      by_cases hd₃: d = 35
      . -- d = 5 * 7 = 35
        apply Or.inr (Or.inr hd₃)

      -- exclusion of the above three cases
      simp [hd₁, hd₂, hd₃] at hd

      -- `linarith` will automatically derive conflicts in the following four cases
      by_cases hd₄: d = 105
      . -- d = 3 * 5 * 7 = 105
        linarith
      by_cases hd₅: d = 3
      . -- d = 3
        linarith
      by_cases hd₆: d = 5
      . -- d = 5
        linarith
      by_cases hd₇: d = 7
      . -- d = 7
        linarith
      -- all the above cases are excluded
      simp [hd₄, hd₅, hd₆, hd₇] at hd
      linarith

    . -- d ∈ {15, 21, 35} -> d ∈ r
      rintro (r₁ | r₂ | r₃)
      -- in this case, we check the three roots separately
      . -- r₁ = 15
        simp [r₁]; rfl
      . -- r₂ = 21
        simp [r₂]; rfl
      . -- r₃ = 35
        simp at r₃
        simp [r₃]; rfl
  . -- ∑d∈ {15, 21, 35}, d = 71
    -- only calc is needed, and the set r is certain in this case.
    simp
