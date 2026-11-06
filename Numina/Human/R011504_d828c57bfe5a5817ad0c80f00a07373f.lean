import Mathlib

/- The equation ${{x}^{2}}-{{y}^{2}}=1991$ has ___          ___ integer solutions. -/
theorem number_theory_624904 : Set.encard {(x, y) : ℤ × ℤ | x ^ 2 - y ^ 2 = 1991} = 8 := by
  -- We can compute the solutions by hand.
  -- We list them all.
  suffices H : {(x, y) : ℤ × ℤ | x ^ 2 - y ^ 2 = 1991} = ({(996, 995), (996, -995), (-996, 995), (-996, -995), (96, 85), (96, -85), (-96, 85), (-96, -85)} : Finset _) by
    rw [H, Set.encard_coe_eq_coe_finsetCard]
    simp
  ext p
  constructor
  . rcases p with ⟨x, y⟩
    simp
    intro h
    -- Rewrite x^2 - y^2 as (x + y)(x - y).
    rw [sq_sub_sq] at h
    -- Take the absolute value of both sides.
    have h' : ((x + y) * (x - y)).natAbs = Int.natAbs 1991 := congrArg Int.natAbs h
    simp [Int.natAbs_mul] at h'
    replace h' : (x + y).natAbs ∣ 1991 := Dvd.intro (x - y).natAbs h'
    -- We get that |x + y| is a divisor of 1991.
    -- So it must be one of 1, 11, 181, 1991.
    replace h' : (x + y).natAbs ∈ Nat.divisors 1991 := by simp [h']
    simp [show Nat.divisors 1991 = {1, 11, 181, 1991} by native_decide] at h'
    zify at h'
    -- We now check each case.
    rcases h' with h' | h' | h' | h'
    all_goals
      rw [abs_eq (by simp)] at h'
      rcases h' with h' | h'
      all_goals
        rw [h'] at h
        omega
  . -- Computation is enough.
    revert p
    simp only [Set.mem_setOf_eq, Finset.mem_coe]
    native_decide
