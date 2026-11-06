import Mathlib

/- Let $a$ and $b$ be positive integers such that $a+b^{3}$ is divisible by $a^{2}+3 a b+3 b^{2}-1$. Prove that $a^{2}+3 a b+3 b^{2}-1$ is divisible by the cube of an integer greater than 1 . -/
theorem number_theory_605990 (a b : ℤ) (posa : 0 < a) (posb : 0 < b)
    (hdvd : (a^2 + 3 * a * b + 3 * b^2 - 1) ∣ (a + b^3)) :
    ∃ c, 1 < c ∧ c^3 ∣ (a^2 + 3 * a * b + 3 * b^2 - 1) := by
  -- let Z = a^2+3ab + 3b^2 - 1
  set Z := a^2+3*a*b+3*b^2-1 with Z_def
  have Zpos: 0 < Z := by
    nlinarith [posa, posb]
  have Znat_nz: Z.toNat ≠ 0 := by
    symm; apply ne_of_lt
    exact Int.lt_toNat.mpr Zpos
  have abnat_pos: 0 < (a+b).toNat := by
    have := add_pos posa posb
    exact Int.lt_toNat.mpr this
  -- we can prove Z divide (a+b)^3
  have hz1: Z ∣ (a+b)^3 := by
    -- by problem statement, Z ∣ a+b^3
    -- or exist c, cZ = a+b^3
    rcases hdvd with ⟨c, hc⟩
    -- rearrange terms in Z, (a+b)^3 = (a+c)Z
    have: (a+b)^3 = (a+c)*Z := by
      rw [add_mul, mul_comm c Z, ← hc, Z_def]
      ring
    -- clearly, Z ∣ (a+b)^3
    rw [this]
    exact Int.dvd_mul_left (a + c) Z
  -- rewrite it in a natural number divide form.
  have hz1': Z.toNat ∣ (a+b).toNat^3 := by
    have h1: 0 ≤ a+b := by linarith [posa, posb]
    have h2 := pow_nonneg h1 3
    have: (a+b).toNat^3 = ((a+b)^3).toNat := by
      zify
      rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
    rw [← Int.toNat_of_nonneg h2, ← this,
    ← Int.toNat_of_nonneg (le_of_lt Zpos)] at hz1
    norm_cast at hz1
  -- if exist such c witness Z contain cubic, done.
  -- otherwise, index of each prime factor of Z ≤ 2.
  by_cases h1: ¬ ∀p, Nat.Prime p → p ∣ Z.toNat →
    Nat.factorization Z.toNat p ≤ 2
  · push_neg at h1
    rcases h1 with ⟨p, pp, pdv, pindex⟩
    -- if some p^3 term occur in Z,
    -- obviously p witness Z divisible by cube of some integer.
    use p
    refine ⟨(by simp [pp.one_lt]), ?_⟩
    rw [← Int.toNat_of_nonneg (le_of_lt Zpos)]
    norm_cast
    apply (Nat.Prime.pow_dvd_iff_le_factorization pp Znat_nz).mpr pindex
  push_neg at h1
  -- all prime factor from Z has power index ≤ 2.
  -- therefore Z divide (a+b)^2
  have h2: Z ∣ (a+b)^2 := by
    rw [← Int.toNat_of_nonneg (le_of_lt Zpos),
    ← Int.toNat_of_nonneg (sq_nonneg (a+b))]
    norm_cast
    -- consider prime factorization of Z and (a+b)^2
    -- suffices to prove for every prime factor p frome Z,
    -- index of p in (a+b)^2 ≥ that in Z.
    have sq_tonat: ((a+b)^2).toNat = ((a+b).toNat)^2 := by
      zify
      rw [Int.toNat_of_nonneg (sq_nonneg _),
      Int.toNat_of_nonneg (by linarith [posa, posb])]
    have absqnat_nz: ((a+b).toNat)^2 ≠ 0 := by
      symm; apply ne_of_lt
      apply sq_pos_of_pos abnat_pos
    rw [sq_tonat, ← Nat.factorization_prime_le_iff_dvd Znat_nz absqnat_nz]
    intro p pp
    -- if p not divide Z, trivial.
    by_cases pdvz: ¬ p ∣ Z.toNat
    · simp [Nat.factorization_eq_zero_of_not_dvd pdvz]
    push_neg at pdvz
    -- else if p ∣ Z, then p ∣ a+b since Z ∣ (a+b)^3
    have pdvab: p ∣ (a+b).toNat := by
      have: p ∣ ((a+b).toNat)^3 := by
        apply Dvd.dvd.trans pdvz hz1'
      exact Nat.Prime.dvd_of_dvd_pow pp this
    -- from h1, index of p in Z ≤ 2
    apply le_trans (h1 p pp pdvz) ?_
    -- p ∣ (a+b), so index of p in (a+b) ≥ 1, and ≥ 2 in (a+b)^2.
    rw [Nat.factorization_pow]
    have: 1 ≤ ((a+b).toNat).factorization p := by
      refine (Nat.Prime.dvd_iff_one_le_factorization pp ?_).mp pdvab
      exact abnat_pos.ne'
    simp [this]
  -- from divide relation, Z ≤ (a+b)^2.
  have Zle: Z ≤ (a+b)^2 := by
    apply Int.le_of_dvd ?_ h2
    apply sq_pos_of_pos ?_
    linarith [posa, posb]
  -- but Z = (a+b)^2 + 2b^2+ab-1 > (a+b)^2, contradiction.
  have not_Zle: Z > (a+b)^2 := by
    have: Z = (a+b)^2 + 2*b^2 + (a*b-1) := by ring
    rw [this]
    have h1: a*b-1 ≥ 0 := by
      apply sub_nonneg.mpr
      exact one_le_mul_of_one_le_of_one_le posa posb
    have h2: 2*b^2 > 0 := by
      apply mul_pos (by norm_num) ?_
      apply sq_pos_of_pos posb
    linarith [h1, h2]
  -- thus finish.
  linarith [Zle, not_Zle]