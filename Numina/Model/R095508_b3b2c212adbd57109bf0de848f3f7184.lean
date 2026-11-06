import Mathlib

theorem number_theory_235848 (p q : ℕ) (hp : Odd p) (hq : Odd q) (h : p > q) :
    IsLeast {x | ∃ y, x = y ∧ q + x > p - x} ((p - q + 2) / 2) := by
  constructor
  · -- Let's prove that (p - q + 2) / 2 is in the set
    use (p - q + 2) / 2
    all_goals omega
  · -- Let's prove that (p - q + 2) / 2 is the least such
    intro k hk
    rcases hk with ⟨y, hy_eq, hy_ineq⟩
    -- If k is in the set, then q + k > p - k
    have h1 : q + k > p - k := by
      omega
    -- Now we need to show that k >= (p - q + 2) / 2
    by_contra h'
    push_neg at h'
    -- Assume k < (p - q + 2) / 2
    have h2 : k < (p - q + 2) / 2 := by
      omega
    -- Then we need to derive a contradiction with q + k > p - k
    -- This is done by showing that if k < (p - q + 2) / 2, then q + k ≤ p - k
    -- But since k < (p - q + 2) / 2
    -- Multiply both sides by 2: 2k < p - q + 2
    -- Then 2k < p - q + 2
    -- Also, we know that q + k > p - k, so q + k > p - k
    -- Multiplying by 2: 2q + 2k > 2p - 2k
    -- Now observe:
    -- Multiply 2q + 2k > 2p - 2k by 1 to get the right variable count, and:
    -- If we know 2k >= p - q + 2, then contradiction may arise if multiply it does happen.
    -- This is clear from the arithmetic computation once we multiply.
    have h3 : q + k ≤ p - k := by
      omega
    -- Therefore we get a contradiction with h1
    omega