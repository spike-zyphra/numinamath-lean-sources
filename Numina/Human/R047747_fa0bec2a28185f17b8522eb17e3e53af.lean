import Mathlib

/- Given that $m$ and $n$ are positive integers such that $m\equiv 6\pmod 9$ and $n\equiv 0\pmod 9$, what is the largest integer that $mn$ is necessarily divisible by? -/
theorem number_theory_19013 : IsGreatest {d : ℕ | ∀ (m n : ℕ), 0 < m → 0 < n → m ≡ 6 [MOD 9] → n ≡ 0 [MOD 9] → d ∣ m * n} 27 := by
  constructor
  · -- $27$ is a possible value
    intro m n _ _ hmp hnp
    have dvdm : 3 ∣ m := by
      refine (Nat.ModEq.dvd_iff hmp ?_).mpr ?_
      any_goals
      norm_num
    have dvdn : 9 ∣ n := by
      exact Nat.dvd_of_mod_eq_zero hnp
    show 3 * 9 ∣ m * n
    exact Nat.mul_dvd_mul dvdm dvdn
  -- $27$ is the greatest such value
  intro d din
  -- use $m = 6, n = 9$ we get $d \mid 54$
  have ddvd1 := din 6 9
  have h1 : 6 ≡ 6 [MOD 9] := by
    exact rfl
  have h2 : 9 ≡ 0 [MOD 9] := by
    exact rfl
  simp [h1, h2] at ddvd1
  -- use $m = 6, n = 9$ we get $d \mid 135$
  have ddvd2 := din 15 9
  have h3 : 15 ≡ 6 [MOD 9] := by
    exact rfl
  have h4 : 9 ≡ 0 [MOD 9] := by
    exact rfl
  simp [h3, h4] at ddvd2
  have ddvd : d ∣ Nat.gcd 54 135 := by
    exact Nat.dvd_gcd ddvd1 ddvd2
  norm_num at ddvd
  apply Nat.le_of_dvd (by norm_num) at ddvd
  exact ddvd