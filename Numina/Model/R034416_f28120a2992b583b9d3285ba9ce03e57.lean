import Mathlib

theorem algebra_610650 : IsLeast {x:ℕ | ∃ a b : ℕ, a+b=x ∧ 0<a ∧ 0 < b ∧ a<b ∧ (((a:ℤ)-20) * (b+23) = a * b)} 321 := by
  constructor
  · -- Show that 321 is in the set. We check that for (a,b)=(160,161), we have the equality
    use 160, 161
    all_goals norm_num
  · -- Now show that 321 is minimal
    intro x hx
    rcases hx with ⟨a, b, hsum, ha0, hb0, hab, heq⟩
    by_contra h
    push_neg at h
    -- Assume that x < 321, so we get a contradiction
    have h1 : a + b < 321 := by
      omega
    have eq1 : (23 : ℤ) * (a : ℤ) - 20 * (b : ℤ) = 460 := by
      nlinarith
    -- Since $a$ and $b$ are bounded, we can use exhaustive search
    have h2 : a ≤ 320 := by
      omega
    have h3 : b ≤ 320 := by
      omega
    interval_cases a <;> omega