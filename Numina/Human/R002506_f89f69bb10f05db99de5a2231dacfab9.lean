import Mathlib

open Finset Nat

/- Define $n!!$ to be $n(n-2)(n-4)\cdots 3\cdot 1$ for $n$ odd and $n(n-2)(n-4)\cdots 4\cdot 2$ for $n$ even. When $\sum_{i=1}^{2009} \frac{(2i-1)!!}{(2i)!!}$ is expressed as a fraction in lowest terms, its denominator is $2^ab$ with $b$ odd. Find $\dfrac{ab}{10}$. -/
theorem number_theory_94374 {a b c : ℕ} (hb : Odd b) (habc : (2 ^ a * b).Coprime c)
    (hsum : ∑ i ∈ Icc 1 2009, ((2 * i - 1)‼ : ℚ) / (2 * i)‼ = c / (2 ^ a * b)) :
    (a * b) / 10 = 401 := by
  -- show that 2 ^ (2 * 2009) ∑ i ∈ Icc 1 2009, (2 * i - 1)‼ / (2 * i)‼
  -- is equal to ∑ i ∈ Icc 1 2009, (2 * i).choose i * 2 ^ (2 * 2009 - 2 * i)
  have heq : 2 ^ (2 * 2009) * ∑ i ∈ Icc 1 2009, ((2 * i - 1)‼ : ℚ) / (2 * i)‼ =
      (∑ i ∈ Icc 1 2009, (2 * i).choose i * 2 ^ (2 * 2009 - 2 * i) : ℚ) := by
    rw [mul_sum]
    -- show that 2 ^ (2 * 2009) * (2 * i - 1)‼ / (2 * i)‼ = (2 * i).choose i * 2 ^ (2 * 2009 - 2 * i)
    -- for all i ∈ [1, 2009]
    apply Finset.sum_congr rfl
    simp only [mem_Icc, Nat.reduceMul, and_imp]
    intro i hi1 hi2
    have h0 : ((2 * i)‼ : ℚ) ≠ 0 := by
      norm_cast
      apply Nat.ne_of_gt
      exact doubleFactorial_pos (2 * i)
    -- we have
    -- (2 * i - 1)‼ / (2 * i)‼ = (2 * i - 1)‼ * (2 * i)‼ / ((2 * i)‼ * (2 * i)‼)
    --                         = (2 * i)! / (2 ^ i * i!) ^ 2
    --                         = (2 * i)! / (2 ^ (2 * i) * i! ^ 2)
    rw [←@mul_div_mul_right _ _ ((2 * i)‼ : ℚ) _ _ h0]
    norm_cast
    nth_rw 2 [mul_comm]
    nth_rw 1 [show 2 * i = (2 * i - 1) + 1 by omega]
    rw [←Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
    set e := 4018
    push_cast
    -- multiply both sides by 2 ^ (2 * i)
    apply mul_left_cancel₀ (by norm_num : (2 : ℚ) ^ (2 * i) ≠ 0)
    rw [show 2 ^ i * (i ! : ℚ) * (2 ^ i * i !) = 2 ^ (2 * i) * (i ! * i !) by ring]
    simp_rw [mul_div]
    rw [mul_div_mul_left _ _ (by norm_num), ←mul_assoc, mul_right_comm, ←mul_div]
    -- it is left to prove that
    -- 2 ^ e * (2 * i)! / (i! * i!) = 2 ^ (2 * i) * 2 ^ (e - 2 * i) * (2 * i).choose i
    rw [←pow_add, show 2 * i + (e - 2 * i) = e by omega]
    congr
    replace h0 : (i ! : ℚ) * i ! ≠ 0 := by
      simp only [ne_eq, _root_.mul_eq_zero, cast_eq_zero, or_self]
      exact factorial_ne_zero i
    apply mul_left_cancel₀ h0
    rw [mul_div_cancel₀ _ h0]
    norm_cast
    rw [show 2 * i - 1 + 1 = 2 * i by omega, ←Nat.choose_mul_factorial_mul_factorial (by omega : i ≤ 2 * i)]
    rw [show 2 * i - i = i by omega, mul_rotate]
  rw [hsum] at heq
  set e := 2 * 2009
  apply_fun (2 ^ a * (b : ℚ) * ·) at heq
  have h0 : 2 ^ a * (b : ℚ) ≠ 0 := by simp; exact ne_of_odd_add hb
  rw [mul_div, mul_div_cancel₀ _ h0] at heq
  norm_cast at heq
  -- let s = ∑ i ∈ Icc 1 2009, (2 * i).choose i * 2 ^ (e - 2 * i)
  set s := ∑ x ∈ _, (2 * x).choose x * _
  -- we have 2 ^ e * c = 2 ^ a * b * s
  -- show that b = 1
  have hb : b = 1 := by
    -- b divides 2 ^ e * c
    have hdiv : b ∣ 2 ^ e * c := by use 2 ^ a * s; rw [heq]; ring
    -- b and c are coprime (because 2 ^ a * b and c are coprime)
    have hbc : b.Coprime c := Nat.Coprime.coprime_mul_left habc
    -- we get b divides 2 ^ e and b is odd
    -- we conclude that b = 1
    apply Nat.Coprime.dvd_of_dvd_mul_right hbc at hdiv
    apply Nat.Coprime.eq_one_of_dvd _ hdiv
    apply Nat.Coprime.pow_right
    exact Odd.coprime_two_right hb
  subst hb
  -- we have 2 ^ e * c = 2 ^ a * s
  -- compute the multiplicity of 2 in 2 ^ e * c and in 2 ^ a * s
  apply_fun emultiplicity 2 at heq
  have hm2 (n : ℕ) : emultiplicity 2 (2 ^ n) = n := Nat.Prime.emultiplicity_pow_self Nat.prime_two
  simp_rw [mul_one, emultiplicity_mul Nat.prime_two.prime, hm2] at heq
  -- we have e + emultiplicity 2 c = a + emultiplicity 2 s
  suffices emultiplicity 2 s = 8 by
    -- show that emultiplicity 2 s = 8 implies a = 4010 and 4010 / 10 = 401
    simp_rw [e, this] at heq
    have hc : c ≠ 0 := by
      contrapose! hsum
      simp [hsum]
      apply _root_.ne_of_gt
      apply sum_pos _ (by norm_num)
      intro i _
      positivity
    have hfin : FiniteMultiplicity 2 c := by rw [Nat.finiteMultiplicity_iff]; omega
    rw [FiniteMultiplicity.emultiplicity_eq_multiplicity hfin] at heq
    norm_cast at heq
    -- from c ≠ 0 it follows that multiplicity 2 c = 0 (because 2 does not divide c)
    suffices multiplicity 2 c = 0 by omega
    rw [multiplicity_eq_zero]
    contrapose! habc
    apply Nat.not_coprime_of_dvd_of_dvd one_lt_two _ habc
    use 2 ^ (a - 1)
    rw [show 2 * 2 ^ (a - 1) = 2 ^ (1 + (a - 1)) by ring, show 1 + (a - 1) = a by omega, mul_one]
  -- prove some auxiliary results about multiplicities
  -- of factorials and binomial coefficients
  have hfin (n : ℕ) : FiniteMultiplicity 2 n.factorial :=
    Nat.finiteMultiplicity_iff.mpr ⟨by norm_num, Nat.factorial_pos _⟩
  have emult_fact_eq_mult (n : ℕ) : emultiplicity 2 n ! = multiplicity 2 n ! := by
    exact FiniteMultiplicity.emultiplicity_eq_multiplicity (hfin n)
  have emult_choose_eq_mult (n : ℕ) : emultiplicity 2 ((2 * n).choose n) = multiplicity 2 ((2 * n).choose n) := by
      apply FiniteMultiplicity.emultiplicity_eq_multiplicity
      rw [Nat.finiteMultiplicity_iff]
      norm_num
      apply Nat.choose_pos
      omega
  -- show that emultiplicity 2 ((2 * n).choose n) + emultiplicity 2 n! = n
  have hm_choose (n : ℕ) : emultiplicity 2 ((2 * n).choose n) + emultiplicity 2 n ! = n := by
    -- we have (2 * n).choose n * n! * n! = (2 * n)!
    have heq := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    apply_fun emultiplicity 2 at heq
    simp_rw [show 2 * n - n = n by omega, emultiplicity_mul Nat.prime_two.prime] at heq
    -- emultiplicity (2 * n)! = emultiplicity n! + n
    rw [Nat.Prime.emultiplicity_factorial_mul Nat.prime_two] at heq
    simp_rw [emult_fact_eq_mult, emult_choose_eq_mult] at heq ⊢
    norm_cast at heq ⊢
    omega
  -- let t e i = (2 * i).choose i * 2 ^ (e - 2 * i)
  set t := fun (e i : ℕ) => (2 * i).choose i * 2 ^ (e - 2 * i)
  -- it follows that emultiplicity 2 (t e i) = e - i - emultiplicity 2 i!
  have hmt {e i : ℕ} (h : 2 * i ≤ e) : emultiplicity 2 (t e i) = e - i - emultiplicity 2 i ! := by
    have heq := hm_choose i
    simp_rw [t, emultiplicity_mul Nat.prime_two.prime, hm2]
    simp_rw [emult_choose_eq_mult, emult_fact_eq_mult] at heq ⊢
    norm_cast at heq ⊢
    omega
  -- prove that emultiplicity 2 (∑ i ∈ [1, n + 1], f i) = emultiplicity 2 (f (n + 1))
  -- if emultiplicity 2 (f j) < emultiplicity 2 (f i) for all i < j
  have emult_sum (n : ℕ) (f : ℕ → ℕ) (hf : ∀ i j, 1 ≤ i → i < j → j ≤ n + 1 → emultiplicity 2 (f j) < emultiplicity 2 (f i)) :
      emultiplicity 2 (∑ i ∈ Icc 1 (n + 1), f i) = emultiplicity 2 (f (n + 1)) := by
    -- proof by induction
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have emult_cast (n : ℕ) : emultiplicity 2 n = emultiplicity 2 (n : ℤ) := by
        rw [show (2 : ℤ) = (2 : ℕ) by norm_num, Int.natCast_emultiplicity]
      simp_rw [emult_cast]
      -- we have emultiplicity 2 (a + b) = emultiplicity b
      -- when emultiplicity 2 b < emultiplicity 2 a
      rw [cast_add, emultiplicity_add_of_gt]
      simp_rw [←emult_cast]
      rw [ih]
      apply hf _ _ (by omega) (by omega) (by omega)
      intros
      apply hf <;> omega
  rw [emult_sum]
  -- we have emultiplicity 2 s = emultiplicity 2 ((2 * 2009).choose 2009)
  --                           = 2009 - emultiplicity 2009!
  · rw [hmt (show 2 * (2008 + 1) ≤ e by norm_num)]
    suffices h : multiplicity 2 2009 ! = 2001 by rw [emult_fact_eq_mult, h]; norm_cast
    -- show that multiplicity 2 2009! = 2001 using a formula for the multiplicity
    -- of 2 in n!
    have := @Nat.Prime.sub_one_mul_multiplicity_factorial 2009 _ Nat.prime_two
    norm_num at this
    exact this
  · intro i j hi hij hj
    -- it is left to show that emultiplicity 2 (t e j) < emultiplicity 2 (t e i)
    -- for i < j
    rw [hmt (by omega), hmt (by omega), emult_fact_eq_mult, emult_fact_eq_mult]
    -- we need to show that e - (j + multiplicity 2 j!) < e - (i + multiplicity 2 i!)
    norm_cast
    simp_rw [Nat.sub_sub]
    suffices j + multiplicity 2 j ! ≤ e ∧ multiplicity 2 i ! ≤ multiplicity 2 j ! by omega
    constructor
    -- j + multiplicity 2 j! ≤ e
    -- it follows from the inequality multiplicity 2 j! < j if j ≠ 0
    · have h := Nat.emultiplicity_two_factorial_lt (show j ≠ 0 by omega)
      rw [emult_fact_eq_mult] at h
      norm_num at h
      omega
    -- show that multiplicity 2 i! ≤ multiplicity 2 j! for i ≤ j to finish the proof
    · rw [FiniteMultiplicity.multiplicity_le_multiplicity_iff (hfin _) (hfin _)]
      -- suppose that 2 ^ d divides i!
      intro n ⟨d, hd⟩
      -- we have j! = i! * (i + 1).ascFactorial (j - i)
      -- so 2 ^ d divides j!
      rw [show j = i + (j - i) by omega, ← Nat.factorial_mul_ascFactorial]
      use d * (i + 1).ascFactorial (j - i)
      rw [hd, mul_assoc]