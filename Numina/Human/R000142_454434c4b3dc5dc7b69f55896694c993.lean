import Mathlib

/- Show that 45 is a pseudoprime to the bases 17 and 19. -/
theorem number_theory_4819 {n a b : ℕ} (hn : n = 45) (ha : a = 17) (hb : b = 19):
    Nat.FermatPsp n a ∧ Nat.FermatPsp n b := by
  /- 原答案错误，以下为重写的正确证明。 -/
  simp [Nat.FermatPsp, Nat.ProbablePrime]
  constructor
  . refine ⟨?_, by rw [hn]; norm_num, by rw [hn]; norm_num⟩
    /- 不难验证: 17^4 ≡ 1 [MOD 45] -/
    have : a^4 ≡ 1 [MOD n] := by rw [ha, hn]; decide
    /- 进而可得: 17^44 = (17^4)^11 ≡ 1 [MOD 45] -/
    have := Nat.ModEq.pow 11 this
    rw [← pow_mul, show 4*11=44 by norm_num, one_pow] at this
    symm at this
    rw [Nat.modEq_iff_dvd' (by rw [ha]; norm_num)] at this
    nth_rw 2 [hn]
    rw [show 45 - 1 = 44 by norm_num]
    exact this
  refine ⟨?_, by rw [hn]; norm_num, by rw [hn]; norm_num⟩
  /- 不难验证: 19^2 ≡ 1 [MOD 45] -/
  have : b^2 ≡ 1 [MOD n] := by rw [hb, hn]; decide
  /- 进而可得: 19^44 = (19^2)^22 ≡ 1 [MOD 45] -/
  have := Nat.ModEq.pow 22 this
  rw [← pow_mul, show 2*22=44 by norm_num, one_pow] at this
  symm at this
  rw [Nat.modEq_iff_dvd' (by rw [hb]; norm_num)] at this
  nth_rw 2 [hn]
  rw [show 45 - 1 = 44 by norm_num]
  exact this
