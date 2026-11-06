import Mathlib

/- Let $a$ and $b$ be integers (not necessarily positive). Prove that $a^{3}+5 b^{3} \neq 2016$. -/
theorem number_theory_609561 (a b : ℤ) :
    a ^ 3 + 5 * b ^ 3 ≠ 2016 := by
  -- If a ^ 3 + 5 * b ^ 3 = 2016
  intro h
  -- We take the equation modulo 7
  have k := congrArg (Int.cast : ℤ → ZMod 7) h
  -- So a ^ 3 + 5 * b ^ 3 = 0 mod 7
  simp [show 2016 = (0 : ZMod 7) by decide] at k
  -- Cubes are either 0, 1, or 6 mod 7
  -- So a ^ 3 + 5 * b ^ 3 = 0 mod 7 implies that a and b are both 0 mod 7
  have lem (x y : ZMod 7) : x ^ 3 + 5 * y ^ 3 = 0 → x = 0 ∧ y = 0 := by
    -- We consider all the cases
    fin_cases x <;> fin_cases y
    all_goals
      simp
    all_goals
      -- x ^ 3 + 5 * y ^ 3 ≠ 0 mod 7
      intro H
      absurd H
      decide
  -- So a and b are both 0 mod 7
  -- In other words, 7 ∣ a and 7 ∣ b
  obtain ⟨ha, hb⟩ := lem a b k
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hb
  -- So 7 ^ 3 ∣ a ^ 3 and 7 ^ 3 ∣ b ^ 3
  obtain ⟨s, hs⟩ : 7 ^ 3 ∣ a ^ 3 := pow_dvd_pow_of_dvd ha 3
  obtain ⟨t, ht⟩ : 7 ^ 3 ∣ b ^ 3 := pow_dvd_pow_of_dvd hb 3
  rw [hs, ht] at h
  -- But 7 ^ 3 does not divide 2016, a contradiction
  clear * - h
  omega
