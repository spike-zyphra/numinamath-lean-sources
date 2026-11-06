import Mathlib

theorem number_theory_106683 (a b c : ℕ)
  (h0 : PythagoreanTriple a b c)
  (co_ab : Nat.Coprime a b)
  (co_bc : Nat.Coprime b c)
  (co_ac : Nat.Coprime a c):
  Odd c ∧ ((Even a ∧ Odd b) ∨ (Odd a ∧ Even b)) := by

  have odd_sq_mod4 {n:ℕ} (hn: Odd n):
    n^2 ≡ 1 [MOD 4] := by
    have: Odd (n:ℤ) := by exact (Int.odd_coe_nat n).mpr hn
    replace := Int.sq_mod_four_eq_one_of_odd this
    exact Int.natCast_modEq_iff.mp this

  have even_sq_mod4 {n:ℕ} (hn: Even n):
    n^2 ≡ 0 [MOD 4] := by
    rw [even_iff_exists_two_mul] at hn
    rcases hn with ⟨m, rfl⟩
    rw [Nat.modEq_zero_iff_dvd]
    rw [mul_pow]
    exact Dvd.dvd.mul_right (by norm_num) _

  have odd_of_co_even {m n: ℕ} (co: Nat.Coprime m n)
    (hn: Even m): Odd n := by
    rw [← Nat.not_even_iff_odd]
    rintro hm
    absurd co
    rw [Nat.Prime.not_coprime_iff_dvd]
    use 2
    refine ⟨(by norm_num), ?_, ?_⟩
    · exact even_iff_two_dvd.mp hn
    · exact even_iff_two_dvd.mp hm

  have parity_cases {m n:ℕ} (co: Nat.Coprime m n):
    (Even m ∧ Odd n) ∨ Odd m := by
    rcases (Nat.even_or_odd m) with evenm | oddm
    · have := odd_of_co_even co evenm
      simp [evenm, this]
    · simp [oddm]

  have even_odd_sq_add {m n:ℕ} (hm: Even m) (hn: Odd n):
    ¬ m^2 + n^2 ≡ 0 [MOD 4] := by
    have h1: m^2 + n^2 ≡ 0+1 [MOD 4] := by
      apply Nat.ModEq.add ?_ ?_
      · apply even_sq_mod4 hm
      · apply odd_sq_mod4 hn
    rintro h2
    have h3: 0+1 ≡ 0 [MOD 4] := h1.symm.trans h2
    contradiction


  have odd_odd_sq_add {m n:ℕ} (hm: Odd m) (hn: Odd n):
    ¬ m^2 + n^2 ≡ 0 [MOD 4] := by
    have h1: m^2 + n^2 ≡ 1+1 [MOD 4] := by
      apply Nat.ModEq.add ?_ ?_
      · apply odd_sq_mod4 hm
      · apply odd_sq_mod4 hn
    rintro h2
    have h3: 1+1 ≡ 0 [MOD 4] := h1.symm.trans h2
    contradiction

  have co_sq_add_mod4 {m n: ℕ} (co: Nat.Coprime m n):
    ¬ m^2 + n^2 ≡ 0 [MOD 4] := by
    rcases parity_cases co with ⟨evenm, oddn⟩ | oddm
    · apply even_odd_sq_add evenm oddn
    · rcases (Nat.even_or_odd n) with evenn | oddn
      · rw [add_comm]
        apply even_odd_sq_add evenn oddm
      · apply odd_odd_sq_add oddm oddn


  dsimp [PythagoreanTriple] at h0
  simp only [← pow_two] at h0
  norm_cast at h0

  have oddc: Odd c := by
    rw [← Nat.not_even_iff_odd]
    rintro hc
    have h1 := even_sq_mod4 hc
    rw [← h0] at h1
    absurd h1
    apply co_sq_add_mod4 co_ab

  rcases parity_cases co_ab with ⟨evena, oddb⟩ | odda
  · simp [oddc, evena, oddb]
  · rcases (Nat.even_or_odd b) with evenb | oddb
    · simp [oddc, odda, evenb]
    · have h1: a^2 + b^2 ≡ 1 [MOD 4] := by
        rw [h0]
        apply odd_sq_mod4 oddc
      have h2: a^2 + b^2 ≡ 1+1 [MOD 4] := by
        apply Nat.ModEq.add ?_ ?_
        · apply odd_sq_mod4 odda
        · apply odd_sq_mod4 oddb
      have h3: 1 ≡ 1+1 [MOD 4] := h1.symm.trans h2
      contradiction