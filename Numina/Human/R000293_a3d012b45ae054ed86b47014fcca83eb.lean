import Mathlib

/- Let  $n$  be an integer. Show that a natural number  $k$  can be found for which, the following applies with a suitable choice  of signs:   $$ n = \pm 1^2 \pm 2^2  \pm 3^2  \pm  ... \pm k^2 $$  -/
theorem number_theory_8840 (n : ℤ) :
    ∃ k : ℕ, 0 < k ∧ ∃ s : ℕ → ℤ, (∀ i, s i = 1 ∨ s i = - 1) ∧
    n = ∑ i ∈ Finset.Icc 1 k, s i * i ^ 2 := by
  -- We assume 0≤n Without loss of generality.
  wlog hn : 0 ≤ n
  . push_neg at hn
    have neg_n_nonneg : 0 ≤ -n := by omega
    rcases this _ neg_n_nonneg with ⟨k, hk, ⟨s, hs, hns⟩⟩
    use k
    constructor
    . exact hk
    let t : ℕ → ℤ := fun i => - (s i)
    use t
    constructor
    . intro i
      dsimp [t]
      exact (hs i).elim (fun h => by norm_num [h]) (fun h => by norm_num [h])
    rw [← mul_right_inj' (show -1 ≠ 0 by norm_num), Finset.mul_sum]
    convert hns using 1
    . ring
    apply Finset.sum_congr rfl
    simp [t]
  -- We use the fact that
  -- $$ n^2-(n+1)^2-(n+2)^2+(n+3)^2=4.
  have key (m : ℤ) : m ^ 2 - (m + 1) ^ 2 - (m + 2) ^ 2 + (m + 3) ^ 2 = 4 := by ring
  let pat : ℕ → ℤ := fun n =>  match n % 4 with
    | 0 => 1
    | 1 => 1
    | 2 => -1
    | 3 => -1
    | _ => 1 -- junk value
  have patmod4 (n : ℕ) : pat n = pat (n % 4) := by simp [pat]
  have pat4k_add (k : ℕ) (n : ℕ) : pat (4 * k + n) = pat n := by
    nth_rw 1 [patmod4]
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, zero_add,
      Nat.mod_mod, eq_comm]
    exact patmod4 _
  have keySum {n : ℕ} {s : ℕ → ℤ} (hs : ∀ i > n, s i = pat (i - n)) (k : ℕ) :
      ∑ i ∈ Finset.Ioc n (4 * k + n), s i * i ^ 2 = 4 * k := by
    induction' k with k ih
    . simp
    rw [show 4*(k+1)+n=(4*k+n)+1+1+1+1 by ring]
    repeat rw [Finset.sum_Ioc_succ_top (by omega)]
    rw [ih]
    repeat rw [hs _ (by omega)]
    rw [show 4 * k + n + 1 - n = 4 * k + 1 by omega,
      show 4 * k + n + 1 + 1 - n = 4 * k + 2 by omega,
      show 4 * k + n + 2 + 1 - n = 4 * k + 3 by omega,
      show 4 * k + n + 3 + 1 - n = 4 * (k + 1) + 0 by omega]
    repeat rw [pat4k_add]
    simp only [pat]
    push_cast
    have (a b c d e : ℤ) : a + b + c + d + e = a + (b + c + d + e) := by ring
    rw [mul_add, this, add_left_cancel_iff]
    rw [one_mul, neg_one_mul, ← sub_eq_add_neg, neg_one_mul, ← sub_eq_add_neg,
      one_mul, mul_one]
    convert key (4 * k + n + 1) using 1
  rcases eq_or_ne n 0 with hn0 | hnpos
  -- If n = 0, then n = 1^2 - 2^2 - 3^2 + 4^2 - 5^2 + 6^2 + 7^2 - 8^2
  . use 8
    constructor
    . norm_num
    let s : ℕ → ℤ := fun n => match n with
      | 1 => 1
      | 2 => -1
      | 3 => -1
      | 4 => 1
      | 5 => -1
      | 6 => 1
      | 7 => 1
      | 8 => -1
      | _ => 1 -- junk value
    use s
    constructor
    . intros
      dsimp [s]
      split <;> norm_num
    rw [show Finset.Icc 1 8 = Finset.Ico 1 9 from rfl, Finset.sum_Ico_eq_sum_range]
    simpa [Finset.sum_range_succ, s]
  have n_div_four := Int.ediv_add_emod n 4
  have : 0 ≤ n % 4 := Int.emod_nonneg _ (by norm_num)
  have : n % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases n % 4
  -- If n % 4 = 0, we use the fact that $$ n^2-(n+1)^2-(n+2)^2+(n+3)^2=4. $$.
  . use n.natAbs
    constructor
    . omega
    let s : ℕ → ℤ := fun n => match n % 4 with
      | 0 => 1
      | 1 => 1
      | 2 => -1
      | 3 => -1
      | _ => 1 -- junk value
    use s
    constructor
    . intros
      dsimp [s]
      split <;> norm_num
    have : 4 ∣ n.natAbs := by zify; rw [dvd_abs]; use n / 4; linear_combination -n_div_four
    rcases this with ⟨k, hk⟩
    rw [hk, show Finset.Icc 1 (4 * k) = Finset.Ioc 0 (4 * k + 0) from rfl, keySum]
    zify at hk
    rwa [abs_of_pos (by omega)] at hk
    . intros
      rfl
  -- If n % 4 = 1, notice that 1 = 1^2
  . use n.natAbs
    constructor
    . omega
    let s : ℕ → ℤ := fun n => if n = 1 then
      1
    else match (n - 1) % 4 with
      | 0 => 1
      | 1 => 1
      | 2 => -1
      | 3 => -1
      | _ => 1 -- junk value
    use s
    constructor
    . intros
      dsimp [s]
      split; norm_num
      split <;> norm_num
    have : 4 ∣ n.natAbs - 1 := by
      zify
      rw [Nat.cast_sub (by omega), Int.natCast_natAbs, Nat.cast_one, abs_of_pos (by omega)]
      use n / 4
      linear_combination -n_div_four
    rcases this with ⟨k, hk⟩
    rw [show n.natAbs = 4 * k + 1 by omega, ← Finset.sum_Ioc_add_eq_sum_Icc (by omega), keySum]
    simp [s]
    zify at hk
    rw [Nat.cast_sub (by omega), Int.natCast_natAbs, Nat.cast_one, abs_of_pos (by omega)] at hk
    linear_combination hk
    . intro i hi
      dsimp [s]
      split; linarith
      rfl
  -- If n % 4 = 2, notice that 2 = -1^2 -2^2 -3^2 + 4^2
  . use 4 * (n.natAbs / 4 + 1)
    constructor
    . omega
    let s : ℕ → ℤ := fun n => if n = 1 then
      -1
    else if n = 2 then
      -1
    else if n = 3 then
      -1
    else if n = 4 then
      1
    else match (n - 4) % 4 with
      | 0 => 1
      | 1 => 1
      | 2 => -1
      | 3 => -1
      | _ => 1 -- junk value
    use s
    constructor
    . intros
      dsimp [s]
      iterate 4 split; norm_num
      split <;> norm_num
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (by omega),
      show Finset.Ioc 1 _ = Finset.Icc 2 _ by rfl,
      ← Finset.sum_Ioc_add_eq_sum_Icc (by omega),
      show Finset.Ioc 2 _ = Finset.Icc 3 _ by rfl,
      ← Finset.sum_Ioc_add_eq_sum_Icc (by omega),
      show Finset.Ioc 3 _ = Finset.Icc 4 _ by rfl,
      ← Finset.sum_Ioc_add_eq_sum_Icc (by omega),
      show 4 * (n.natAbs / 4 + 1) = 4 * (n.natAbs / 4) + 4 by ring, keySum]
    simp [s]
    rw [abs_of_pos (by omega)]
    linear_combination -n_div_four
    . intro i hi
      dsimp [s]
      iterate 4 split; linarith
      rfl
  -- If n % 4 = 3, notice that 3 = -1^2 + 2^2
  . use 4 * (n.natAbs / 4) + 2
    constructor
    . omega
    let s : ℕ → ℤ := fun n => if n = 1 then
      -1
    else if n = 2 then
      1
    else match (n - 2) % 4 with
      | 0 => 1
      | 1 => 1
      | 2 => -1
      | 3 => -1
      | _ => 1 -- junk value
    use s
    constructor
    . intros
      dsimp [s]
      split; norm_num
      split; norm_num
      split <;> norm_num
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (by omega),
      show Finset.Ioc 1 (4 * _ + 2) = Finset.Icc 2 _ from rfl,
      ← Finset.sum_Ioc_add_eq_sum_Icc (by omega),
      keySum]
    simp [s]
    rw [abs_of_pos (by omega)]
    linear_combination -n_div_four
    . intro i hi
      dsimp [s]
      split; linarith
      split; linarith
      split
      any_goals rename_i h; rw [patmod4, h]
      have : (i - 2) % 4 < 4 := Nat.mod_lt _ (by norm_num)
      interval_cases (i - 2) % 4
      all_goals tauto
