import Mathlib

namespace number_theory_98033

def is_pretty (n : ℕ) (k : ℕ) := n.divisors.card = k ∧ k ∣ n

end number_theory_98033

open number_theory_98033

/- Call a positive integer n k-pretty if n has exactly k positive divisors
and n is divisible by k. For example, 18 is 6-pretty. Let S be the sum of positive
integers less than 2019 that are 20-pretty. Find S / 20​. -/
theorem number_theory_98033 : (∑ᶠ n ∈ {n | n < 2019 ∧ is_pretty n 20}, n) / 20 = 472 := by
  -- show that 20 ∣ n iff n = 2 ^ a * 5 ^ b * k with a ≥ 2, b ≥ 1 and k.Coprime 2 and k.Coprime 5
  have hdiv {n : ℕ} (h0 : n ≠ 0) : 20 ∣ n ↔ ∃ a b k, a ≥ 2 ∧ b ≥ 1 ∧ k.Coprime 2 ∧ k.Coprime 5 ∧ n = 2 ^ a * 5 ^ b * k := by
    constructor
    · intro hdiv
      -- prove a lemma which shows that a number n ≠ 0 can be represented as n = p ^ a * k
      -- with k.Coprime p for any prime p which divides n
      have hfactor {p n : ℕ} (hp : p.Prime) (h0 : n ≠ 0) (hpn : p ∣ n) : ∃ k, n = p ^ n.factorization p * k ∧ k.Coprime p := by
        use n / p ^ n.factorization p
        simp [Nat.ordProj_mul_ordCompl_eq_self]
        apply Nat.Coprime.symm
        exact Nat.coprime_ordCompl hp h0
      -- we get n = 2 ^ n.facrorization 2 * x with x.Coprime 2 (since 2 ∣ n)
      obtain ⟨x, hxn, hx2⟩ := hfactor Nat.prime_two h0 (dvd_trans (by norm_num) hdiv)
      -- show that 5 ∣ x
      have h5 : 5 ∣ x := by
        have h25 : Nat.Coprime 5 (2 ^ n.factorization 2) := by
          exact Nat.Coprime.pow_right _ rfl
        apply Nat.Coprime.dvd_of_dvd_mul_left h25
        rw [←hxn]
        exact dvd_trans (by norm_num) hdiv
      -- show that x ≠ 0
      have hx0 : x ≠ 0 := by
        contrapose! h0
        rw [hxn, h0, mul_zero]
      -- we get x = 5 ^ x.factorization 5 * y with y.Coprime 5 (since 5 ∣ x)
      obtain ⟨y, hyx, hy2⟩ := hfactor Nat.prime_five hx0 h5
      -- use the multiplicity of 2 in n (a), the multiplicity of 5 in x (b), and y (k)
      use n.factorization 2, x.factorization 5, y
      constructorm* _ ∧ _
      · apply (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h0).mp
        apply dvd_trans _ hdiv
        norm_num
      · apply (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hx0).mp
        exact h5
      · rw [hyx] at hx2
        rw [Nat.coprime_mul_iff_left] at hx2
        exact hx2.2
      · assumption
      · nth_rw 1 [hxn, hyx, mul_assoc]
    · intro ⟨a, b, k, ha, hb, hk2, _, heq⟩
      have : 2 ^ a * 5 ^ b = 20 * 2 ^ (a - 2) * 5 ^ (b - 1) := by
        nth_rw 1 [show a = (a - 2) + 2 by omega, show b = (b - 1) + 1 by omega]
        ring
      rw [heq, this, mul_assoc, mul_assoc]
      exact Nat.dvd_mul_right 20 _
  -- number of divisors of (2 ^ a * 5 ^ b * k) = (a + 1) * (b + 1) * (number of divisors of k)
  have hcard {a b k : ℕ} (hk : k.Coprime 2 ∧ k.Coprime 5) :
      (2 ^ a * 5 ^ b * k).divisors.card = (a + 1) * (b + 1) * k.divisors.card := by
    have hk25 : (2 ^ a * 5 ^ b).Coprime k := by
      rw [Nat.coprime_mul_iff_left]
      constructor
      all_goals {
        apply Nat.Coprime.pow_left
        rw [Nat.coprime_comm]
        tauto
      }
    have h25 : (2 ^ a).Coprime (5 ^ b) := by
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.pow_right
      norm_num
    -- use the fact that a.Coprime b implies that d(a * b) = d(a) * d(b) where d(n) is the number of divisors of n
    rw [Nat.Coprime.card_divisors_mul hk25, Nat.Coprime.card_divisors_mul h25]
    congr
    all_goals {
      -- finish the proof using the basic properties of the arithmetic function σ₀
      rw [←ArithmeticFunction.sigma_zero_apply]
      rw [ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num)]
    }
  -- the equation (a + 1) * (b + 1) * c = 20 has only two solutions over ℕ
  -- when a ≥ 2, b ≥ 1, and 2 ^ a * 5 ^ b < 2019
  have hab_eq {a b c : ℕ} (heq : (a + 1) * (b + 1) * c = 20) (ha : a ≥ 2) (hb : b ≥ 1) (hlt : 2 ^ a * 5 ^ b < 2019) : (a = 4 ∧ b = 1 ∧ c = 2 ∨ a = 4 ∧ b = 3 ∧ c = 1) := by
    have ha_div : (a + 1) ∈ (20).divisors := by
      simp; use (b + 1) * c; rw [←heq, mul_assoc]
    have hdivs : (20).divisors = {1, 2, 4, 5, 10, 20} := by decide
    simp [hdivs] at ha_div
    -- a + 1 ∣ 20, consider all possible values of a
    rcases ha_div with h | h | h | h | h | h <;> try omega
    -- if a = 3 then b + 1 ∣ 5, consider all possible values of b
    · replace heq : (b + 1) * c = 5 := by rw [h] at heq; linarith
      have hb_div : (b + 1) ∈ (5).divisors := by simp; use c; rw [←heq]
      replace hdivs : (5).divisors = {1, 5} := by decide
      simp [hdivs] at hb_div
      rcases hb_div with h1 | h1
      · omega
      simp [h, h1] at hlt
    -- if a = 4 then b + 1 ∣ 4, consider all possible values of b
    · replace heq : (b + 1) * c = 4 := by rw [h] at heq; linarith
      have hb_div : (b + 1) ∈ (4).divisors := by simp; use c; rw [←heq]
      replace hdivs : (4).divisors = {1, 2, 4} := by decide
      simp [hdivs] at hb_div
      rcases hb_div with h1 | h1 | h1
      · omega
      · left; simp [h, h1] at heq ⊢; omega
      · right; simp [h, h1] at heq ⊢; assumption
    -- if a = 9 then 2 ^ a * 5 ^ b > 2019
    · suffices 2 ^ a * 5 ^ b > 2019 by omega
      simp [h]
      suffices 5 ^ b ≥ 5 by omega
      apply Nat.le_self_pow
      omega
    -- if a = 19 then 2 ^ a > 2019
    · suffices 2 ^ a * 5 ^ b > 2019 by omega
      simp [h]
      suffices 5 ^ b > 0 by omega
      exact Nat.pos_of_neZero (5 ^ b)
  -- a number p is prime iff it has exactly two divisors.
  -- This fact is missing in Mathlib.
  have hprime_div (p : ℕ) : p.Prime ↔ p.divisors.card = 2 := by
    constructor
    · intro hp
      rw [Nat.Prime.divisors hp, Finset.card_pair]
      exact Ne.symm (Nat.Prime.ne_one hp)
    · intro h
      rw [Nat.prime_def]
      rcases (show p = 0 ∨ p = 1 ∨ 2 ≤ p by omega) with hp | hp | hp
      · simp [hp] at h
      · simp [hp] at h
      · refine ⟨hp, ?_⟩
        intro m hmp
        suffices p.divisors = {1, p} by
          have hmem := Nat.mem_divisors.mpr ⟨hmp, by omega⟩
          simp [this] at hmem
          assumption
        have ⟨x, y, hxy, hpdiv⟩ := Finset.card_eq_two.mp h
        have h1 : 1 ∈ p.divisors := by rw [Nat.one_mem_divisors]; omega
        have h2 : p ∈ p.divisors := by apply Nat.mem_divisors_self; omega
        simp [hpdiv] at h1 h2 ⊢
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · omega
          · rw [h1, h2]
        · rcases h2 with h2 | h2
          · rw [h1, h2, Finset.pair_comm]
          · omega
  -- now we can show that the set from the theorem statement is equal to the set
  -- {80 * p | p is prime, p ≠ 2, p ≠ 5, 80 * p < 2019} ∪ {2000}
  have hset : {n | n < 2019 ∧ is_pretty n 20} = (80 * ·) '' {p | p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ 80 * p < 2019} ∪ {2000} := by
    ext n; simp [is_pretty]; constructor
    · intro ⟨hn, hncard, hndiv⟩
      have hn0 : n ≠ 0 := by contrapose! hncard; simp [hncard]
      rw [hdiv hn0] at hndiv
      -- since 20 ∣ n, we can represent it as 2^a * 5^b * k with a ≥ 2, b ≥ 1 and k.Coprime 10
      obtain ⟨a, b, k, ha, hb, hk2, hk5, hneq⟩ := hndiv
      rw [hneq, hcard ⟨hk2, hk5⟩] at hncard
      have hk : k ≥ 1 := by cases k; norm_num at hk2; omega
      have hineq : 2 ^ a * 5 ^ b < 2019 := by
        apply lt_of_le_of_lt _ hn
        simp [hneq, hk]
      -- we proved that there are only two solutions to the number of divisors equation
      -- consider two cases
      cases hab_eq hncard ha hb hineq with
      | inl h =>
        rw [← hprime_div] at h
        right; use k
        simp [h.1, h.2.1] at hneq
        rw [hneq] at hn
        simp [hneq, hn, h]
        constructor
        exact (Nat.coprime_primes h.2.2 Nat.prime_two).mp hk2
        exact (Nat.coprime_primes h.2.2 (by norm_num)).mp hk5
      | inr h =>
        left
        simp [hneq, h.1, h.2.1]
        rw [Finset.card_eq_one] at h
        have ⟨x, xeq⟩ := h.2.2
        rw [← Nat.divisors_inj, Nat.divisors_one, xeq]
        suffices 1 ∈ k.divisors by simp [xeq] at this; simp [this]
        exact Nat.one_mem_divisors.mpr (by omega)
    · intro h
      cases h with
      | inl h =>
        rw [h]; norm_num
        rw [show 2000 = 2 ^ 4 * 5 ^ 3 * 1 by norm_num]
        rw [hcard ⟨by norm_num, by norm_num⟩]
        simp
      | inr h =>
        obtain ⟨p, ⟨hp, hp2, hp5, hplt⟩, hpn⟩ := h
        simp [← hpn, hplt]
        refine ⟨?_, by apply Dvd.dvd.mul_right; norm_num⟩
        rw [show 80 * p = 2 ^ 4 * 5 ^ 1 * p by omega]
        rw [hcard ⟨(Nat.coprime_primes hp Nat.prime_two).mpr hp2, (Nat.coprime_primes hp (by norm_num)).mpr hp5⟩]
        rw [(hprime_div p).mp hp]
  -- it is left to find all primes p such that p ≠ 2, p ≠ 5, and 80 * p < 2019
  have hps : {p | p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ 80 * p < 2019} = {3, 7, 11, 13, 17, 19, 23} := by
    have eq1 : {p | p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ 80 * p < 2019} = {p | p ≠ 2 ∧ p ≠ 5 ∧ p ∈ (List.filter Nat.Prime (List.range 26)).toFinset} := by
      have ineq p : 80 * p < 2019 ↔ p < 26 := by omega
      ext p; simp [ineq]; tauto
    have eq2 : List.filter Nat.Prime (List.range 26) = [2, 3, 5, 7, 11, 13, 17, 19, 23] := by decide
    simp [eq1, eq2]
    ext p; simp; omega
  rw [hset, hps, finsum_mem_eq_toFinset_sum]
  simp