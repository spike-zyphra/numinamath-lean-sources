import Mathlib

/-
Let $ \left[x\right]$ denote the greatest integer not exceeding $x$.
Find the last two digits of
$\left[ \frac { 1 } { 3 } \right] + \left[ \frac { 2 } { 3 } \right] + \left[ \frac { 2 ^ { 2 } } { 3 } \right] + \cdots + \left[ \frac { 2 ^ { 2 0 1 4 } } { 3 } \right]$.

Answer: 15.
-/
theorem number_theory_624215 :
  (∑ i ∈ Finset.range 2015, ⌊(2 ^ i : ℚ) / 3⌋) % 100 = 15 := by

  -- Our first claim is that if $n$ is odd, then there exists $k$
  -- such that $2^n=3k+2$.
  have claim1 (n : ℕ) (hn : Odd n) : ∃ k, 2 ^ n = 3 * k + 2 := by
    have : 2 ≡ 2 ^ n [MOD 3] := by
      symm
      obtain ⟨ r, hr ⟩ := hn
      simp [hr, pow_add, pow_mul]
      calc
        _ ≡ 1 ^ r * 2 [MOD 3] := by refine Nat.ModEq.mul ?_ rfl
                                    exact Nat.ModEq.pow r rfl
        _ ≡ 2 [MOD 3] := by rw [one_pow, one_mul]
    rw [Nat.modEq_iff_dvd] at this
    obtain ⟨ r, hr ⟩ := this
    have : ∃ m : ℕ, m = r := by
      refine CanLift.prf r ?_
      have : 2 ^ n ≥ 2 := by refine Nat.le_self_pow ?_ 2; exact Nat.ne_of_odd_add hn
      omega
    obtain ⟨ m, hm ⟩ := this
    use m
    omega

  -- It follows that if $n$ is odd, then $(2^n - 2/3)3=2^n-2$.
  have claim2 (n : ℕ) (hn : Odd n) : (2 ^ n - 2 : ℤ) / 3 * 3 = 2 ^ n - 2 := by
    obtain ⟨ k, hk ⟩ := claim1 n hn
    zify at hk
    rw [hk]
    norm_num
    omega

  -- If $n$ is odd, then $\lfloor 2^n/3 \rfloor= (2^n-2)/3).$
  have hnOdd (n : ℕ) (hn : Odd n) : ⌊ (2 ^ n : ℚ) / 3⌋ = ((2 ^ n : ℚ) - 2 : ℚ) / 3 := by
    obtain ⟨ k, hk ⟩ := claim1 n hn
    qify at hk
    simp [hk]
    simp [add_div]
    norm_num

  -- If $n$ is even, then $\lfloor 2^n/3 \rfloor= (2^n-1)/3).$
  have hnEven (n : ℕ) (hn : Even n) : ⌊ (2 ^ n : ℚ) / 3⌋ = ((2 ^ n : ℚ) - 1 : ℚ) / 3 := by
    have : ∃ k, 2 ^ n = 3 * k + 1:= by
      have : 1 ≡ 2 ^ n [MOD 3] := by
        symm
        obtain ⟨ r, hr ⟩ := hn
        rw [← two_mul] at hr
        simp [hr, pow_add, pow_mul]
        calc
          _ ≡ 1 ^ r [MOD 3] := by exact Nat.ModEq.pow r rfl
          _ ≡ 1 [MOD 3] := by rw [one_pow]
      rw [Nat.modEq_iff_dvd] at this
      obtain ⟨ r, hr ⟩ := this
      have : ∃ m : ℕ, m = r := by
        refine CanLift.prf r ?_
        have : 2 ^ n ≥ 1 := by exact Nat.one_le_two_pow
        omega
      obtain ⟨ m, hm ⟩ := this
      use m
      omega
    obtain ⟨ k, hk ⟩ := this
    qify at hk
    simp [hk]
    simp [add_div]
    norm_num

  -- We show that $\sum_{i=0}^{2k} \lfloor 2^i/3 \rfloor = (2^{2k+1}-2)/3-k$.
  have h (k : ℕ) : ∑ i ∈ Finset.range (2 * k + 1), ⌊(2 ^ i : ℚ) / 3⌋ = (2 ^ (2 * k + 1) - 2) / 3 - k := by
    have : ∑ i ∈ Finset.range (2 * k + 1), ⌊(2 ^ i : ℚ) / 3⌋ =
           ∑ i ∈ Finset.range k, (⌊(2 ^ (2 * i + 1) : ℚ) / 3⌋ + ⌊(2 ^ (2 * (i + 1)) : ℚ) / 3⌋) := by
      rw [Finset.sum_range_eq_add_Ico]
      rw [pow_zero]
      have : ⌊(1 : ℚ) / 3⌋ = 0 := by norm_num
      rw [this, zero_add]
      . induction k with
        | zero => simp
        | succ i ih =>
          rw [mul_add]
          rw [Finset.sum_Ico_succ_top]
          rw [Finset.sum_Ico_succ_top]
          rw [ih]
          rw [Finset.sum_range_succ]
          rw [mul_add, mul_one]
          ring
          . apply Nat.zero_lt_succ
          . apply Nat.zero_lt_succ
      . apply Nat.zero_lt_succ

    rw [this]
    clear this
    have : ∑ i ∈ Finset.range k, (⌊(2 ^ (2 * i + 1) : ℚ) / 3⌋ + ⌊(2 ^ (2 * (i + 1))  : ℚ) / 3⌋ : ℚ) =
           ∑ i ∈ Finset.range k, ((2 ^ (2 * i + 1) : ℚ) / 3 + (2 ^ (2 * (i + 1)) : ℚ) / 3 - 1) := by
      have : ∀ i ∈ Finset.range k, (⌊(2 ^ (2 * i + 1) : ℚ) / 3⌋ + ⌊(2 ^ (2 * (i + 1)) : ℚ) / 3⌋)
             = (2 ^ (2 * i + 1) : ℚ) / 3 + (2 ^ (2 * (i + 1)) : ℚ) / 3 - 1 := by
        intro i ih
        obtain hOdd := hnOdd (2 * i + 1) (by simp)
        obtain hEven := hnEven (2 * (i + 1)) (by simp)
        rw [hOdd, hEven]
        ring
      refine Finset.sum_congr rfl ?_
      exact fun x a => this x a
    qify
    rw [this]
    clear this
    have : ∑ i ∈ Finset.range k, ((2 ^ (2 * i + 1) : ℚ) / 3 + (2 ^ (2 * (i + 1)) : ℚ) / 3 - 1) =
           ∑ i ∈ Finset.range k, ((2 ^ (2 * i + 1) : ℚ) / 3 + (2 ^ (2 * (i + 1)) : ℚ) / 3) - ↑k := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ]
        rw [Finset.sum_range_succ]
        rw [ih]
        have : @HAdd.hAdd ℕ ℕ ℕ instHAdd k 1 = (k : ℚ) + 1 := by exact Mathlib.Tactic.Ring.inv_add rfl rfl
        rw [this]
        ring

    rw [this]
    clear this

    have : ∑ i ∈ Finset.range k, ((2 ^ (2 * i + 1) : ℚ) / 3 + (2 ^ (2 * (i + 1)) : ℚ) / 3) =
           (∑ i ∈ Finset.range (2 * k), (2 ^ (i + 1) : ℚ)) / 3 := by
      induction k with
      | zero => simp
      | succ i ih =>
        rw [Finset.sum_range_succ]
        rw [mul_add]
        rw [Finset.sum_range_succ]
        rw [Finset.sum_range_succ]
        rw [mul_one]
        rw [add_assoc (2 * i)]
        rw [← two_mul, mul_one, ih]
        ring
    rw [this]
    clear this
    simp
    field_simp
    induction k with
    | zero => simp
    | succ k ih =>
      rw [mul_add]
      have : 2 * 1 = 1 + 1 := by norm_num
      rw [this, ← add_assoc]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [ih]
      obtain t1 := claim2 (2 * k + 1) (by norm_num)
      obtain t2 := claim2 (2 * k + 1 + 1 + 1) (by norm_num)
      qify at t1 t2
      rw [t1, t2]
      ring

  -- Setting $k=1007$, we obtain that $\sum_{i=0}^{2014} \lfloor 2^i/3 \rfloor = (2^{2015}-2)/3-1007$.
  obtain g := h 1007
  have : 2 * 1007 + 1 = 2015 := by norm_num
  rw [this] at g
  clear this
  rw [g]
  
  -- A simple calculation shows that $(2^{2015}-2)/3-1007$ 
  -- leaves a remainder of 15 when divided by 100.
  omega
