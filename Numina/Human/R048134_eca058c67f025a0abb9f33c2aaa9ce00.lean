import Mathlib

/- Show that no integer of the form \( n^{3} + 1 \) is a prime, other than \( 2 = 1^{3} + 1 \). -/
theorem number_theory_4488 : {n : ℕ | n.Prime ∧ ∃ m, n = m ^ 3 + 1} = {2} := by
  ext n
  refine ⟨fun ⟨hn, m, hm⟩ => ?_, fun hn => ?_⟩
  -- Show if n is prime and n=m^3+1 then n=2.
  · simp only [Set.mem_singleton_iff]
    -- Use the formula of sum of two cubes.
    have : n = (m + 1) * (m ^ 2 - m + 1) := by
      zify
      rw [hm, Int.ofNat_sub, ← sub_eq_zero]
      · push_cast; ring
      · zify; apply Int.le_self_pow_two
    -- As n is prime, it must be m=0 or m=1.
    replace : m = 0 ∨ m = 1 := by
      by_contra h
      simp only [not_or] at h
      have h₁ : m + 1 ≠ 1 := by simpa using h.1
      have h₂ : m ^ 2 - m + 1 ≠ 1 := by
        simp only [ne_eq, add_left_eq_self]
        convert_to m * (m - 1) ≠ 0
        zify
        rw [Int.ofNat_sub, Int.ofNat_sub]
        · push_cast; ring_nf
        · omega
        · zify; apply Int.le_self_pow_two
        · exact Nat.mul_ne_zero h.1 (by omega)
      exact Nat.not_prime_mul' this.symm h₁ h₂ hn
    cases' this with this this
    -- m=0 is impossible, because n=0^3+1=1 is not prime.
    · rw [this] at hm
      rw [hm] at hn
      absurd hn
      decide
    -- m=1 means n=2 which is desired.
    · rwa [this] at hm
  -- Show n=2 satisfy that n is prime and n=m^3+1
  · simp only [Set.mem_singleton_iff] at hn
    rw [hn]
    simp only [Set.mem_setOf_eq, Nat.reduceEqDiff]
    constructor
    · decide
    · use 1; simp
