import Mathlib

/- Definition of mutually relative prime, same as in Problem 4518 and 4520. -/
def MutuallyRelativePrime (s : Finset ℤ) := s.gcd id = 1

/- Show that if \( a, b, \) and \( c \) are mutually relatively prime nonzero integers,
  then \( (a, bc) = (a, b)(a, c) \). -/
theorem number_theory_4517
    {a b c : ℤ} (rel : MutuallyRelativePrime {a, b, c}) : a.gcd (b * c) = a.gcd b * a.gcd c := by
  simp only [MutuallyRelativePrime, Finset.gcd_insert, id_eq,
    Finset.gcd_singleton, normalize_apply, Int.normUnit_eq] at rel
  -- Unfolds the definition of `MutuallyRelative`.
  replace rel : gcd a (gcd b c) = 1 := by
    split_ifs at rel
    · simpa using rel
    · simpa [gcd_neg] using rel
  replace rel : a.natAbs.gcd (b.natAbs.gcd c.natAbs) = 1 := calc
    _ = a.gcd (b.natAbs.gcd c.natAbs) := by simp [Int.gcd_def]
    _ = (gcd a (b.natAbs.gcd c.natAbs)).natAbs := by apply Int.natAbs_gcd
    _ = (gcd a (b.gcd c)).natAbs := by simp [Int.gcd_def]
    _ = (gcd a (gcd b c)).natAbs := by simp only [Int.natAbs_gcd]; congr
    _ = 1 := by simp [rel]
  simp only [Int.gcd_def, Int.natAbs_mul]
  -- Replace the goal to natural numbers.
  set x := a.natAbs
  set y := b.natAbs
  set z := c.natAbs
  -- Apply theorem `Nat.gcd_eq_iff` to use the definition of `gcd` in mathematical sense:
  -- `gcd(a, b)` is the maximum number `n` such that `n | a, n | b`.
  rw [Nat.gcd_eq_iff]
  refine ⟨?_, ?_, fun c hc hc' => ?_⟩
  · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · refine Nat.coprime_of_dvd (fun p hp hy hz => ?_)
      rw [Nat.dvd_gcd_iff] at hy hz
      have dvd := Nat.dvd_gcd_iff.mpr ⟨hy.1, Nat.dvd_gcd_iff.mpr ⟨hy.2, hz.2⟩⟩
      rw [rel, Nat.dvd_one] at dvd
      rw [dvd] at hp
      revert hp
      decide
    · apply Nat.gcd_dvd_left
    · apply Nat.gcd_dvd_left
  · apply Nat.mul_dvd_mul <;> apply Nat.gcd_dvd_right
  · refine Nat.dvd_trans ?_ (Nat.gcd_mul_dvd_mul_gcd _ _ _)
    rw [Nat.dvd_gcd_iff]
    exact ⟨hc, hc'⟩
