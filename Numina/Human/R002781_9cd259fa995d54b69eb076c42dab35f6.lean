import Mathlib

/- Find all pairs of prime numbers $(p, q)$ such that $p \mid 5^{q}+1$ and $q \mid 5^{p}+1$. -/

-- lemma that p ∣ 5^q + 1 for prime p, q means p and 5 are coprime as otherwise p ∣ 5^p  so p ∣ 1
lemma l_five_coprime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (h : p ∣ 5 ^ q + 1) : Nat.Coprime p 5 := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  by_contra h'
  have : p ∣ 5 ^ q := by
    apply dvd_pow h'
    exact hq.ne_zero
  rw [Nat.dvd_add_right this] at h
  simp at h
  rw [h] at hp
  norm_num at hp

-- divisors of p * q are 1, p, q, p * q
lemma l_dvd_prime_mul_prime {p q n : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    n ∣ p * q ↔ n = 1 ∨ n = p ∨ n = q ∨ n = p * q := by
  simp only [dvd_mul, Nat.dvd_prime, hp, hq, and_or_left, or_and_right,
    exists_or, exists_and_left, exists_eq_left, one_mul, mul_one]
  tauto

-- prime divisors of 4
lemma l_dvd_four {p : ℕ} (hp : Nat.Prime p) (h: p ∣ 4) : p = 2 := by
  replace h : p ∈ {1, 2, 4} := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
  simp at h
  obtain rfl | rfl | rfl := h
  any_goals norm_num at hp
  simp

-- prime divisors of 26
lemma l_dvd_twenty_six {p : ℕ} (hp : Nat.Prime p) (h: p ∣ 26) : p = 2 ∨ p = 13 := by
  replace h : p ∈ {1, 2, 13, 26} := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
  simp at h
  obtain rfl | rfl | rfl | rfl := h
  any_goals norm_num at hp
  all_goals simp

-- prime divisors of 24
lemma l_dvd_twenty_four {p : ℕ} (hp : Nat.Prime p) (h: p ∣ 24) : p = 2 ∨ p = 3 := by
  replace h : p ∈ {1, 2, 3, 4, 6, 8, 12, 24} := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
  simp at h
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := h
  any_goals norm_num at hp
  all_goals simp

-- prime divisors of 126
lemma l_dvd_hundred_twenty_six {p : ℕ} (hp : Nat.Prime p) (h: p ∣ 126) : p = 2 ∨ p = 3 ∨ p = 7 := by
  replace h : p ∈ {1, 2, 3, 6, 7, 9, 14, 18, 21, 42, 63, 126} := Nat.mem_divisors.mpr ⟨h, by norm_num⟩
  simp at h
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := h
  any_goals norm_num at hp
  all_goals simp

theorem number_theory_112214 (p q : ℕ) : (p.Prime ∧ q.Prime ∧
    p ∣ 5^q + 1 ∧ q ∣ 5^p + 1) ↔ ((p, q) = (2, 2) ∨ (p, q) = (2, 13) ∨ (p, q) = (13, 2) ∨
    (p, q) = (3, 3) ∨ (p, q) = (3, 7) ∨ (p, q) = (7, 3)) := by
  constructor
  . rintro ⟨hp, hq, h1, h2⟩
    -- wlog assume q ≤ p, as otherwise we get half of results
    wlog h : q ≤ p
    . obtain ⟨rfl, rfl⟩  | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :=
        this q p hq hp h2 h1 (le_of_not_le h)
      all_goals simp
    -- 5, p and 5, q are coprime
    have hp5 := l_five_coprime hp hq h1
    have hq5 := l_five_coprime hq hp h2
    -- 5 ^ p = -1 (mod q)
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at h2
    push_cast at h2
    replace h2 : 5 ^ p = (-1 : ZMod q) := by linear_combination h2
    replace h2 := congrArg (· ^ 2) h2
    simp at h2
    ring_nf at h2
    -- in particular 5 ^ (2p) = 1 in units group of modulo q
    let u := ZMod.unitOfCoprime _ hq5.symm
    rw [show (5 : ZMod q) = u by norm_cast,
        show (1 : ZMod q) = ↑(1 : (ZMod q)ˣ) by norm_cast] at h2
    norm_cast at h2
    -- so order of 5 divides 2p, there are 4 options 1, p, 2, 2p
    rw [← orderOf_dvd_iff_pow_eq_one, l_dvd_prime_mul_prime hp (by norm_num)] at h2
    have h' := pow_orderOf_eq_one u
    obtain h2 | h2 | h2 | h2 := h2
    -- if order is 1, then q ∣ 5^1 - 1 so q = 2
    . rw [h2] at h'
      rw [Units.ext_iff] at h'
      push_cast at h'
      rw [pow_one, show u = (5 : ZMod q) by norm_cast, show (5 : ZMod q) = ↑(5 : ℕ) by norm_cast,
          show (1 : ZMod q) = ↑(1 : ℕ) by norm_cast, ZMod.eq_iff_modEq_nat, Nat.ModEq.comm,
          Nat.modEq_iff_dvd' (by norm_num)] at h'
      simp at h'
      replace h' := l_dvd_four hq h'
      -- so p ∣ 26, then p = 2 or 13
      rw [h'] at h1 ⊢
      simp
      norm_num at h1
      apply l_dvd_twenty_six hp h1
    -- if order is p then p ∣ q - 1 (by fermat's little theorem),but then q ≤ p ≤ q - 1 impossible
    . haveI : Fact (Nat.Prime q) := ⟨hq⟩
      have h'' := ZMod.units_pow_card_sub_one_eq_one q u
      rw [← orderOf_dvd_iff_pow_eq_one, h2] at h''
      have : 2 ≤ q := Nat.Prime.two_le hq
      replace h'' := Nat.le_of_dvd (by omega) h''
      omega
    -- if order is 2 then q ∣ 5^2 - 1 so q = 2 or q = 3
    . rw [h2] at h'
      rw [Units.ext_iff] at h'
      push_cast at h'
      rw [show u ^ 2 = (5 ^ 2 : ZMod q) by simp [u], show (5 ^ 2 : ZMod q) = ↑(5 ^ 2 : ℕ) by norm_cast,
         show (1 : ZMod q) = ↑(1 : ℕ) by norm_cast, ZMod.eq_iff_modEq_nat, Nat.ModEq.comm,
         Nat.modEq_iff_dvd' (by norm_num)] at h'
      norm_num at h'
      replace h' := l_dvd_twenty_four hq h'
      obtain rfl | rfl := h'
      -- for q = 2, like before we get p = 2 or 13
      . simp; norm_num at h1
        apply l_dvd_twenty_six hp h1
      -- for q = 3, we get p ∣ 5^3 + 1 = 126, so p = 2, 3, 7, but p = 2 contradicts q ≤ p
      . simp; norm_num at h1
        obtain rfl | rfl | rfl := l_dvd_hundred_twenty_six hp h1
        any_goals norm_num at h
        all_goals simp
    -- if order is 2p then as before 2p ∣ q - 1 by fermat's little theorem and then q ≤ p ≤ 2p ≤ q - 1 impossible
    . haveI : Fact (Nat.Prime q) := ⟨hq⟩
      have h'' := ZMod.units_pow_card_sub_one_eq_one q u
      rw [← orderOf_dvd_iff_pow_eq_one, h2] at h''
      have : 2 ≤ q := Nat.Prime.two_le hq
      replace h'' := Nat.le_of_dvd (by omega) h''
      omega
  -- plug in all values and see that they satisfy conditions
  . rintro h
    obtain ⟨rfl, rfl⟩  | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
    all_goals norm_num