import Mathlib

/- 6. Find all pairs of natural numbers $n$ and $k$ for which $(n+1)^{k}=$ $n!+1$. (As usual, $n!$ denotes the product of all natural numbers not exceeding $n$. For example, $4!=1 \cdot 2 \cdot 3 \cdot 4$.) -/
theorem number_theory_222114 (n k : ℕ) :
    (n + 1)^k = Nat.factorial n + 1 ↔
    (n = 1 ∧ k = 1) ∨ (n = 2 ∧ k = 1) ∨ (n = 4 ∧ k = 2) := by
  -- solutions are valid
  symm; constructor <;> intro h
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
    all_goals decide
  -- 4 cases: k = 0, k = 1, k = 2, 3 ≤ k
  obtain rfl | rfl | rfl | hl : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by clear * -; omega
  · -- k can't be 0
    simp only [pow_zero] at h
    simp only [self_eq_add_left] at h
    exfalso; revert h
    simp only [imp_false]
    exact Nat.factorial_ne_zero n
  · -- k = 1, n = 1 or 2
    simp only [pow_one, Nat.add_left_inj] at h
    obtain nh | rfl | rfl | rfl : 3 ≤ n ∨ n = 0 ∨ n = 1 ∨ n = 2 := by clear * -; omega
    · have mt := Nat.lt_factorial_self nh
      linarith
    all_goals norm_num at h
    all_goals norm_num
  · -- k = 2, n = 4
    have ft (h : 5 ≤ n) : (n + 1)^2 < n.factorial + 1 := by
      clear * - h
      induction n with
      | zero => norm_num at h
      | succ n IH =>
        obtain rfl | j : n = 4 ∨ 5 ≤ n := by omega
        · decide
        simp only [Nat.factorial, Nat.succ_eq_add_one]
        ring_nf
        have m := IH j
        ring_nf at m
        nlinarith
    obtain jj | rfl | rfl | rfl | rfl | rfl : 5 ≤ n ∨ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by clear * -; omega
    · have := ft jj
      linarith
    all_goals simp only [Nat.factorial] at h
    all_goals norm_num at h
    all_goals norm_num
  · -- we probe n from 0 to 5
    obtain rfl | rfl | rfl | rfl | rfl | rfl | jj : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n := by clear * -; omega
    -- if n = 0
    · simp only [zero_add, one_pow, Nat.factorial_zero, Nat.reduceAdd, OfNat.one_ne_ofNat] at h
    -- if n = 1
    · simp only [Nat.reduceAdd, Nat.factorial_one] at h
      rw [Nat.pow_eq_self_iff (by norm_num)] at h; subst k; norm_num at hl
    -- if n = 2
    · simp only [Nat.reduceAdd, Nat.factorial_two] at h
      rw [Nat.pow_eq_self_iff (by norm_num)] at h; subst k; norm_num at hl
    -- if n = 3
    · rw [(by decide : Nat.factorial 3 + 1 = 7)] at h; norm_num at h
      have dk : 4^k < 4^2 := by linarith
      rw [Nat.pow_lt_pow_iff_right] at dk
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      all_goals norm_num at *
    -- if n = 4
    · rw [(by decide : Nat.factorial 4 + 1 = 25)] at h; norm_num at h
      rw [(by norm_num : 25 = 5^2)] at h
      have pow_right_inj {a m n : ℕ} (ha : 2 ≤ a) : a ^ m = a ^ n ↔ m = n :=
        (Nat.pow_right_injective ha).eq_iff
      rw [pow_right_inj (by norm_num)] at h
      simp only [OfNat.ofNat_ne_one, h, and_self, Nat.reduceEqDiff, or_true]
    -- if n = 5
    · rw [(by decide : Nat.factorial 5 + 1 = 121)] at h; norm_num at h
      have dk : 6^k < 6^3 := by linarith
      rw [Nat.pow_lt_pow_iff_right] at dk
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      all_goals norm_num at *
    -- 6 ≤ n
    -- parity argument: n! + 1 is odd, therefore (n + 1)^k is odd, therefore n + 1 is odd, therefore n is even
    have ng := @Nat.dvd_factorial 2 n (by norm_num) (by linarith)
    have lr : n.factorial ≡ 0 [MOD 2] := by exact Nat.modEq_zero_iff_dvd.mpr ng
    have nr := Nat.ModEq.add_left 1 lr
    rw [add_comm] at nr
    norm_num at nr
    rw [←h] at nr
    -- we arrive at (n+1)^k is odd
    have o1 : Odd ((n+1)^k) := by exact Nat.odd_iff.mpr nr
    have o2 : Odd (↑((n+1)^k) : ℤ) := by exact (Int.odd_coe_nat ((n + 1) ^ k)).mpr o1
    push_cast at o2
    rw [Int.odd_pow' (by linarith)] at o2
    have ns : Odd (1 : ℤ) := by decide
    have bb := Odd.sub_odd o2 ns
    -- now n is even
    norm_num at bb
    clear lr nr o1 o2 ns
    obtain ⟨m, hm⟩ := bb
    -- we factor out n^2
    have brof : 4 * m * m ∣ (m + m).factorial := by
      have ga : 3 ≤ m := by linarith
      clear * - ga
      -- now we turn this into finset product so we can take the factors out
      rw [←Finset.prod_range_add_one_eq_factorial]
      -- now we take 2, 2 * m and m out
      have nh := Finset.sdiff_union_of_subset (s₂ := Finset.range (m + m)) (s₁ := {1, 2 * m - 1, m - 1}) (by {
        simp only [Subset, Finset.mem_insert, Finset.mem_singleton, Finset.mem_range,
          forall_eq_or_imp, forall_eq]
        omega
      })
      rw [←nh]
      rw [Finset.prod_union]
      · -- here we multiply the 3 terms we take out
        have mid : ∏ x ∈ {1, 2 * m - 1, m - 1}, (x + 1) = 4 * m * m := by
          rw [(by aesop : ({1, 2 * m - 1, m - 1} : Finset ℕ) = {1} ∪ {2 * m - 1} ∪ {m - 1})]
          rw [Finset.prod_union, Finset.prod_union]
          simp only [Finset.prod_singleton, Nat.reduceAdd]
          rw [(by omega : 2 * m - 1 + 1 = 2 * m), (by omega : m - 1 + 1 = m)]
          ring
          all_goals simp only [Finset.disjoint_singleton_right, Finset.mem_singleton,
            Nat.pred_eq_succ_iff, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            mul_eq_left₀, Finset.mem_union, Finset.mem_singleton, Nat.pred_eq_succ_iff, zero_add, not_or]
          all_goals omega
        rw [mid]
        exact
          Nat.dvd_mul_left (4 * m * m) (∏ x ∈ Finset.range (m + m) \ {1, 2 * m - 1, m - 1}, (x + 1))
      -- justify why we can take out the 3 terms
      simp only [Finset.disjoint_insert_right, Finset.mem_sdiff, Finset.mem_range,
        Finset.mem_insert, Finset.mem_singleton, true_or, not_true_eq_false, and_false,
        not_false_eq_true, Nat.pred_eq_succ_iff, zero_add, ne_eq, OfNat.ofNat_ne_zero, mul_eq_left₀,
        or_true, Finset.disjoint_singleton_right, and_self]
    rw [(by ring : 4 * m * m = (m + m) * (m + m)), ←hm] at brof
    -- n^2 is now a divisor
    -- next up we examine the binomial expansion
    have p := Commute.add_pow (x := n) (y := 1) (by exact Commute.one_right n) k
    simp only [one_pow, mul_one, Nat.cast_id] at p
    -- we take out the first 2 terms
    have decomp : Finset.range (k + 1) = Finset.range 2 ∪ Finset.Ico 2 (k + 1) := by
      ext g
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    simp only [decomp] at p
    rw [Finset.sum_union (by simp [Finset.disjoint_left]; omega)] at p
    simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero,
      Nat.choose_zero_right, mul_one, pow_one, Nat.choose_one_right] at p
    have mg := Finset.sum_Ico_add (fun x => n^x * k.choose x) 0 (k - 1) 2
    norm_num at mg
    rw [(by omega : k - 1 + 2 = k + 1)] at mg
    simp only [← mg, pow_add] at p
    simp_rw [mul_assoc] at p
    rw [←Finset.mul_sum] at p
    clear mg
    generalize hh : ∑ i ∈ Finset.range (k - 1), n ^ i * k.choose (2 + i) = xx
    rw [hh] at p
    have fn : n.factorial = n * k + n^2 * xx := by linarith
    rw [fn] at brof
    -- now we get n^2 ∣ n*k
    have fw : n * n ∣ (n^2 * xx) := by
      ring_nf
      exact Nat.dvd_mul_right (n ^ 2) xx
    rw [←Nat.dvd_add_iff_left fw] at brof
    -- derive n ∣ k
    rw [Nat.mul_dvd_mul_iff_left (by linarith)] at brof
    -- so this means n ≤ k
    have mf := Nat.le_of_dvd (by linarith) brof
    -- now it's time to do an induction argument
    have rg : (n + 1)^n ≤ (n + 1)^k := Nat.pow_le_pow_right (by norm_num) mf
    -- next up compare (n + 1)^n with the factorial
    have fl : n.factorial + 1 < (n + 1)^n := by
      clear * - jj
      induction n with
      | zero => norm_num at jj
      | succ n IH =>
        obtain rfl | hd : n = 5 ∨ 6 ≤ n := by omega
        · decide
        rw [Nat.pow_succ]
        simp only [Nat.factorial]
        have ka := IH hd
        have rg : (n + 1)^n ≤ (n + 1 + 1)^n := Nat.pow_le_pow_left (by norm_num) n
        -- conclude
        nlinarith
    -- contradiction
    linarith
