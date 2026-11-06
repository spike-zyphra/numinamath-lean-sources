import Mathlib

theorem number_theory_258524 :
    {r : ℝ | ∃p q : ℕ, p.Prime ∧ q.Prime ∧
          3 * p + 5 * q = 31 ∧
          r = Real.logb 2 (p / (3 * q + 1))
    } = {-3, 0} := by
  ext r
  simp
  constructor
  · rintro ⟨p, hp, q, hq, h, hr⟩
    rw [hr]

    -- Since $p$ and $q$ are primes and $3p + 5q = 31$, let's determine possible values
    have hp : p = 2 ∨ p = 7 := by
      have hmod5 : 3 * p ≡ 1 [MOD 5] := by
        apply Nat.ModEq.trans
        case b => exact 31
        rw [h.symm, Nat.ModEq]
        omega
        rw [Nat.ModEq]
      rw [Nat.ModEq] at hmod5
      omega

    -- We can use obtain to extract the value of $p$
    obtain (hp | hp) := hp
    · -- p = 2
      have hq : q = 5 := by linarith
      rw [hp, hq]
      norm_num
      simp [Real.logb_eq_iff_rpow_eq]
      norm_num
    · -- p = 7
      have hq : q = 2 := by linarith
      rw [hp, hq]
      norm_num

  · rintro (rfl | rfl)
    · -- r = -3
      use 2
      norm_num
      use 5
      norm_num
      simp
      apply Eq.symm
      simp [Real.logb_eq_iff_rpow_eq]
      norm_num
    · -- r = 0
      use 7
      norm_num
      use 2
      norm_num
