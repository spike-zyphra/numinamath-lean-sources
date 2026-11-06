import Mathlib

/- There exists a unique positive integer $a$ for which the sum
$$
U=\sum_{n=1}^{2023}\left\lfloor\dfrac{n^{2}-na}{5}\right\rfloor
$$
 is an integer strictly between $-1000$ and $1000$. For that unique $a$, find $a+U$.
(Note that $\lfloor x\rfloor$ denotes the greatest integer that is less than or equal to $x$.) -/
theorem number_theory_98638 (U a : ℤ) (hu₁ : -1000 ≤  U) (hu₂: U ≤ 1000) (ha_pos: 0 < a) (ha: U = ∑ n ∈ Finset.Icc (1:ℕ) 2023, ⌊(n^2 - n * a) / (5:ℝ)⌋) (ha_uniq: ∀ b > 0, U = ∑ n ∈ Finset.Icc (1:ℕ) 2023, ⌊(n^2 - n * a) / (5:ℝ)⌋ → a = b) : a + U = 944 := by
  -- first we define U', we'll related it to U by showing U' is an upper bound
  set U' := ∑ n ∈ Finset.Icc (1:ℕ) 2023, (n ^ 2 - n * a) / (5:ℝ) with ha'
  have hu_lb : U ≤ U' := by
    rw [ha, ha']
    push_cast
    apply Finset.sum_le_sum
    simp_rw [Int.floor_le]; simp
  --  next we'll show U' has upper bound U + 2023, we'll do this by using a < ⌊a⌋ + 1
  have hu_ub : U' ≤ U + 2023 := by
    rw [ha, ha']
    have h : ∑ n ∈ Finset.Icc (1:ℕ) 2023, (n ^ 2 - n * a) / (5:ℝ) ≤ ∑ n ∈ Finset.Icc (1:ℕ) 2023, (⌊(n ^ 2 - n * a) / (5:ℝ)⌋ + 1) := by
      push_cast
      apply Finset.sum_le_sum
      rintro i hi
      suffices (i ^ 2 - i * a) / (5:ℝ) < ⌊(i ^ 2 - i * a) / (5:ℝ)⌋ + 1 by linarith
      exact Int.lt_floor_add_one _
    have h': ∑ n ∈ Finset.Icc (1:ℕ) 2023, (⌊(n ^ 2 - n * a) / (5:ℝ)⌋ + 1) = (∑ n ∈ Finset.Icc (1:ℕ) 2023, ⌊(n ^ 2 - n * a) / (5:ℝ)⌋) + 2023 := by
      rw [Finset.sum_add_distrib, Finset.sum_const]
      norm_num
    rw [h'] at h
    exact_mod_cast h
  -- now we'll update the bounds by utilizing U's bounds
  replace hu_lb : -1000 ≤ U' := by calc
    (-1000:ℝ) ≤ U := by exact_mod_cast hu₁
    _ ≤ U' := by exact_mod_cast hu_lb
  replace hu_ub : U' ≤ 3023 := by calc
    U' ≤ U + 2023 := by exact_mod_cast hu_ub
    _ ≤ 1000 + 2023 := by gcongr; exact_mod_cast hu₂
    _ ≤ 3023 := by norm_num
  -- we'll prove sum of n and n^2 series as mathlib doesn't have these yet
  have hsum_id (n: ℕ) (hn : 1 ≤ n) : ∑ i ∈ Finset.Icc 1 n, (i:ℝ) = n * (n + 1) / 2 := by
    rw [← Nat.Ico_succ_right]
    induction' n, hn using Nat.le_induction with m hm hm'
    . simp
    . rw [Finset.sum_Ico_succ_top (by omega)]
      rw [hm']
      push_cast
      ring
  have hsum_sq (n: ℕ) (hn : 1 ≤ n) : ∑ i ∈ Finset.Icc 1 n, (i:ℝ)^2 = n * (n + 1) * (2*n+1) / 6 := by
    rw [← Nat.Ico_succ_right]
    induction' n, hn using Nat.le_induction with m hm hm'
    . simp
      norm_num
    . rw [Finset.sum_Ico_succ_top (by omega)]
      rw [hm']
      push_cast
      ring
  -- we'll provide exact value for U' by using the seriess used
  have ha' : U' = 2023 * 2024 * (4047 - 3 * a) / 30 := by calc
    U' = ∑ n ∈ Finset.Icc (1:ℕ) 2023, (n ^ 2/(5:ℝ) + n * -a / (5:ℝ)) := by
      rw [ha', Finset.sum_congr rfl]
      ring_nf; simp
    _ = ∑ n ∈ Finset.Icc (1:ℕ) 2023, (n ^ 2/(5:ℝ)) + ∑ n ∈ Finset.Icc (1:ℕ) 2023, (n * -a/(5:ℝ)) := by
      rw [Finset.sum_add_distrib]
    _ = (2023 * 2024 * 4047) / (30:ℝ) - (a * 2023 * 2024) / (10:ℝ) := by
      rw [← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_mul, hsum_id _ (by norm_num), hsum_sq _ (by norm_num)]
      ring
    _ = 2023 * 2024 * (4047 - 3 * a) / 30 := by ring
  -- now using thebounds, we can prove a = 1349
  rw [ha'] at hu_lb; rw [ha'] at hu_ub
  replace hu_lb : 30 * -1000 ≤ 2023 * 2024 * (4047 - 3 * (a:ℝ)) := by linarith
  replace hu_ub : 2023 * 2024 * (4047 - 3 * (a:ℝ)) ≤ 3023 * 30 := by linarith
  replace hu_lb : 30 * -1000 ≤ 2023 * 2024 * (4047 - 3 * a) := by exact_mod_cast hu_lb
  replace hu_ub : 2023 * 2024 * (4047 - 3 * a) ≤ 3023 * 30 := by exact_mod_cast hu_ub
  have : 4047 - 3 * a = 0 := by omega
  have : a = 1349 := by omega
  subst a
  -- two casting realted lemma that lean seems to not be able to prove further below due to nestedness, so we prove here
  have aux_cast (a b : ℤ) : ↑(a + b) = (a : ℝ) + b := by norm_cast
  have aux_cast' {a b : ℤ} (h: (a: ℝ) = b) : a = b := by norm_cast at h
  -- we prove final formula for U using induction
  have aux₂ (k : ℕ) (hk : 1 ≤ k) : ∑ n ∈ Finset.Ico 1 (5 * k + 1), ⌊(n ^ 2 - n * 1349) / (5:ℝ)⌋ =
    k * (5*k+1) * (10*k+1)/(6:ℝ) - 1349 * k * (5 * k + 1) / 2 - k
      := by
      induction' k, hk using Nat.le_induction with m hm hm'
      . rw [Finset.sum_Ico_succ_top (by norm_num)]
        rw [Finset.sum_Ico_succ_top (by norm_num)]
        rw [Finset.sum_Ico_succ_top (by norm_num)]
        rw [Finset.sum_Ico_succ_top (by norm_num)]
        rw [Finset.sum_Ico_succ_top (by norm_num)]
        simp
        norm_num
      . rw [← Finset.sum_Ico_consecutive (m := 1) (n := 5*m + 1) (k := 5*(m+1) + 1) _ (by omega) (by omega)]
        rw [aux_cast, hm']
        rw [show 5 * (m + 1) + 1 = 5 * m + 6 by ring]
        rw [Finset.sum_Ico_succ_top (by norm_num)]
        rw [Finset.sum_Ico_succ_top (by norm_num)]
        rw [Finset.sum_Ico_succ_top (by norm_num)]
        rw [Finset.sum_Ico_succ_top (by norm_num)]
        rw [Finset.sum_Ico_succ_top (by norm_num)]
        simp
        ring_nf
        have h₁ : ⌊1 / (5 : ℝ)⌋ = 0 := Int.floor_eq_zero_iff.mpr (by norm_num)
        have h₂ : ⌊2 / (5 : ℝ)⌋ = 0 := Int.floor_eq_zero_iff.mpr (by norm_num)
        have h₄ : ⌊4 / (5 : ℝ)⌋ = 0 := Int.floor_eq_zero_iff.mpr (by norm_num)
        have : ⌊ -1348 / (5:ℝ) - m * 1347 + m ^ 2 * 5⌋ = -270 - m * 1347 + m^2 * 5 := by
          rw [show -1348 / (5:ℝ) = 2/5 - 270 by ring]
          rw [show 2 / (5:ℝ) - 270 - ↑m * 1347 + ↑m ^ 2 * 5 = 2 / (5:ℝ) + ↑(-270 - m * 1347 + m ^ 2 * 5 : ℤ) by push_cast;ring]
          rw [Int.floor_add_int, h₂]
          linarith
        rw [this]
        have : ⌊ -2694 / (5:ℝ) - m * 1345 + m ^ 2 * 5⌋ = -539 - m * 1345 + m^2 * 5 := by
          rw [show -2694 / (5:ℝ) = 1/5 - 539 by ring]
          rw [show 1 / (5:ℝ) - 539 - ↑m * 1345 + ↑m ^ 2 * 5 = 1 / (5:ℝ) + ↑(-539 - m * 1345 + m ^ 2 * 5 : ℤ) by push_cast;ring]
          rw [Int.floor_add_int, h₁]
          linarith
        rw [this]
        have : ⌊ -4038 / (5:ℝ) - m * 1343 + m ^ 2 * 5⌋ = -808 - m * 1343 + m^2 * 5 := by
          rw [show -4038 / (5:ℝ) = 2/5 - 808 by ring]
          rw [show 2 / (5:ℝ) - 808 - ↑m * 1343 + ↑m ^ 2 * 5 = 2 / (5:ℝ) + ↑(-808 - m * 1343 + m ^ 2 * 5 : ℤ) by push_cast;ring]
          rw [Int.floor_add_int, h₂]
          linarith
        rw [this]
        have : ⌊ -1076 - m * 1341 + m ^ 2 * (5:ℝ)⌋ = -1076 - m * 1341 + m^2 * 5 := by
          rw [show -1076 - m * 1341 + m ^ 2 * (5:ℝ) = (↑(-1076 - m * 1341 + m ^ 2 * 5 : ℤ): ℝ) by norm_cast]
          rw [Int.floor_intCast]
        rw [this]
        have : ⌊-1344 - m * 1339 + m ^ 2 * (5:ℝ)⌋ = -1344 - m * 1339 + m ^ 2 * 5 := by
          rw [show -1344 - m * 1339 + m ^ 2 * (5:ℝ) = (↑(-1344 - m * 1339 + m ^ 2 * 5 : ℤ): ℝ) by norm_cast]
          rw [Int.floor_intCast]
        rw [this]
        push_cast
        ring
  -- finally by pluggin ing the formula we get value of U, rest is just plugging in
  have : U = -405 := by
    rw [ha]
    have : ∑ n ∈ Finset.Icc (1:ℕ) 2023, ⌊(n ^ 2 - n * 1349) / (5 : ℝ)⌋ = ∑ n ∈ Finset.Ico (1:ℕ) 2021, ⌊(n ^ 2 - n * 1349) / (5 : ℝ)⌋ + ∑ n ∈ Finset.Ico (2021:ℕ) 2024, ⌊(n ^ 2 - n * 1349) / (5 : ℝ)⌋ := by
      rw [Finset.sum_Ico_consecutive _ (by norm_num) (by norm_num)]
      rfl
    push_cast
    rw [this]
    have := aux₂ 404 (by norm_num)
    rw [show 5 * 404 + 1 = 2021 by norm_num] at this
    suffices  ↑(∑ n ∈ Finset.Ico (1:ℕ) 2021, ⌊(n ^ 2 - ↑n * 1349) / (5:ℝ)⌋  + ∑ n ∈ Finset.Ico (2021:ℕ) 2024, ⌊(n ^ 2 - n * 1349) / (5:ℝ)⌋) = (-405: ℝ) by
      clear * - this aux_cast'
      rw [show (-405:ℝ) = ↑(-405:ℤ) by norm_cast] at this
      specialize aux_cast' this
      exact aux_cast'
    rw [aux_cast, this]
    norm_num
    rw [Finset.sum_Ico_succ_top (by norm_num)]
    rw [Finset.sum_Ico_succ_top (by norm_num)]
    rw [Finset.sum_Ico_succ_top (by norm_num)]
    simp
    norm_num
  rw [this]
  simp