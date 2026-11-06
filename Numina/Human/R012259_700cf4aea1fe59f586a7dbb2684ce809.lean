import Mathlib


/- How many positive integers N less than 1000 are there such that the equation x^⌊x⌋ = N has a solution for x? -/
theorem number_theory_94174 : Set.ncard {N : ℕ | N < 1000 ∧ ∃ x : ℝ, x ^ ⌊x⌋ = N} = 412 := by
  -- first prove 0 ≤ x for such n
  have hx_lb (N : ℕ) (x: ℝ) (hx: x ^ ⌊x⌋ = N) : 0 ≤ x := by
    -- to prove, assume opposite and prove contradiction
    by_contra hx_neg
    simp at hx_neg
    have : ⌊x⌋ < 0 := by refine Int.floor_lt.mpr (by norm_cast)
    -- do case work on -1 ≤ x or not
    by_cases h: -1 ≤ x
      -- -1 ≤ x means ⌊x⌋ = -1
    . have : ⌊x⌋ = -1 := by
        apply Int.floor_eq_iff.mpr
        constructor <;> (simp; linarith)
      -- due to odd power, x^⌊x⌋ will be negative, contradiction
      have : N < 0 := by
        rify
        rw [← hx, this]
        refine Odd.zpow_neg (by simp) (by assumption)
      omega
    -- otherwise x < -1, so ⌊x⌋ ≤ -1 and x^⌊x⌋ = (-1)^(⌊x⌋) * (1 / x^-⌊x⌋)
    . simp at h
      have hx_fl : ⌊x⌋ ≤ -1 := by
        apply Int.floor_le_iff.mpr
        simp
        linarith
      have h_x_inv : x^⌊x⌋ = 1 / x^(-⌊x⌋) := by simp
      -- in particular 1 < (-1) ^ (-⌊x⌋) * (1 / x ^ ⌊x⌋) will be used later
      have h' : 1 < (-1) ^ (-⌊x⌋) * (1 / x ^ ⌊x⌋) := by
        calc
        1 < (-1 * x) ^ (-⌊x⌋) := by
          refine (one_lt_zpow_iff_right₀ ?_).mpr ?_
          repeat linarith
        _ = (-1) ^ (-⌊x⌋) * x ^ (-⌊x⌋) := by rw [mul_zpow]
        _ = (-1) ^ (-⌊x⌋) * (1 / x ^ ⌊x⌋) := by
          congr; field_simp
      -- -1's power is 1 or -1, do casework on them
      have h_one_or_minus_one: ((-1):ℝ) ^ (- ⌊x⌋) = 1 ∨ ((-1):ℝ) ^ (- ⌊x⌋) = -1 := by
        refine mul_self_eq_one_iff.mp ?_;
        rw [← @mul_zpow]; simp
      obtain h | h := h_one_or_minus_one
      all_goals (rw [h] at h'; simp at h')
        -- for positive power, x^⌊x⌋ between 0 and 1
      . rw [@one_lt_inv_iff₀] at h'
        have := h'.right
        rw [hx] at this
        norm_cast at this
        -- this implies N = 0, but then, x^⌊x⌋ can't be 0
        have : N = 0 := by omega
        rw [this] at hx
        norm_cast at hx
        have : x = 0 := by exact eq_zero_of_zpow_eq_zero hx
        linarith
        -- for negative power, this implies x^⌊x⌋ is negative, contradiction
      . have : (x ^ ⌊x⌋)⁻¹ < 0 := by linarith
        have : (x ^ ⌊x⌋) < 0 := inv_lt_zero.mp this
        linarith
  -- prove uppwer bound on x, which is 5
  have hx_ub (N : ℕ) (x: ℝ) (hn_ub: N < 1000) (hx: x ^ ⌊x⌋ = N) : x < 5 := by
    have := hx_lb N x hx
    -- x ≥ 5 can't haepeen as then x^⌊x⌋ ≥ 1000
    by_contra h
    simp at h
    have := calc
      5^(5:ℤ) ≤ x^(5:ℤ) := by
        have : 5^(5:ℝ) ≤ x^(5:ℝ) := by
          refine (Real.rpow_le_rpow_iff (by norm_num) (by linarith) (by norm_num)).mpr (by assumption)
        norm_cast at this; norm_cast
      _ ≤ x^⌊x⌋ := by
        gcongr
        linarith
        simp [Int.le_floor]; assumption
      _ = N := by rw [hx]
      _ < 1000 := by norm_cast
    linarith
  -- ⌊x⌋ = k means N ∈ [k^k, (k+1)^k)
  have hn_range₁ (N k: ℕ) (x : ℝ) (hx : x^k = N) (hx' : ⌊x⌋ = k) (hk: k ≠ 0) : N ∈ Set.Ico (k^k) ((k+1)^k) := by
    constructor
    . rify
      rw [← hx]
      gcongr
      have := Int.floor_le x
      rw [hx'] at this
      norm_cast at this
    . rify
      rw [← hx]
      gcongr
      . refine hx_lb N x ?_
        rw [hx']
        norm_cast
      . have := Int.lt_floor_add_one x
        rw [hx'] at this
        norm_cast at this; norm_cast
  -- last fact means N < 1000 and x^⌊x⌋ = N means N ∈ [1, 2), [4, 9), [27, 64), [256, 625) by caswork on ⌊x⌋
  have hn_ranges₁ (N: ℕ) (x : ℝ) (hn_ub: N < 1000) (hx: x ^ ⌊x⌋ = N) : N ∈ Set.Ico 1 2 ∨ N ∈ Set.Ico 4 9 ∨ N ∈ Set.Ico 27 64 ∨ N ∈ Set.Ico 256 625 := by
    have := hx_lb N x hx
    have : 0 ≤ ⌊x⌋ := by exact Int.floor_nonneg.mpr (by assumption)
    have := hx_ub N x hn_ub hx
    have : ⌊x⌋ < 5 := by exact Int.floor_lt.mpr (by assumption)
    interval_cases h: ⌊x⌋
    . simp at hx
      left
      simp
      norm_cast at hx
      omega
    . have := hn_range₁ N 1 x hx h (by norm_num)
      left
      simp at this; simp; omega
    . have := hn_range₁ N 2 x hx h (by norm_num)
      right; left
      simp at this; simp; omega
    . have := hn_range₁ N 3 x hx h (by norm_num)
      right; right; left
      simp at this; simp; omega
    . have := hn_range₁ N 4 x hx h (by norm_num)
      right; right; right
      simp at this; simp; omega
  -- N ∈ [k^k, (k+1)^k) means there is x (N^(1/k)) which satisfies x^⌊x⌋ = N
  have hn_range₂ (N k: ℕ) (hn: (k^k) ≤ N ∧ N < ((k+1)^k)) (hk: k ≠ 0) : ∃ x : ℝ, x ^ ⌊x⌋ = N := by
    use (N ^ ((1:ℝ)/k))
    have : ⌊(N:ℝ) ^ ((1:ℝ)/k)⌋ = k := by
      suffices h: k ≤ (N:ℝ) ^ ((1:ℝ)/k) ∧ (N:ℝ) ^ ((1:ℝ)/k) < k+1 by
        refine Int.floor_eq_iff.mpr ?_
        norm_cast
        norm_cast at h
      constructor
      . calc
          (k:ℝ) ≤ ((k:ℝ)^(k:ℝ)) ^ ((1:ℝ)/k) := by
            rw [← Real.rpow_mul]
            repeat field_simp
          _ ≤ (N:ℝ) ^ ((1:ℝ)/k) := by
            gcongr
            norm_cast
            exact hn.left
      . calc
          (N:ℝ) ^ ((1:ℝ)/k) < ((k+1:ℝ)^(k:ℝ)) ^ ((1:ℝ)/k) := by
            gcongr
            norm_cast
            exact hn.right
          _ = (k+1:ℝ) := by
            rw [← Real.rpow_mul]
            field_simp
            norm_cast; omega
    rw [this]
    have : ((N:ℝ) ^ ((1:ℝ) / k)) ^ (k:ℝ) = N := by
      rw [← Real.rpow_mul]
      field_simp
      simp
    norm_cast at this
  -- last fact implies N ∈ [1, 2), [4, 9), [27, 64), [256, 625) means N ≤ 1000 and there is x^⌊x⌋ = N
  have hn_ranges₂ (N: ℕ) (hn: N ∈ Set.Ico 1 2 ∨ N ∈ Set.Ico 4 9 ∨ N ∈ Set.Ico 27 64 ∨ N ∈ Set.Ico 256 625) : N < 1000 ∧ ∃ x : ℝ, x ^ ⌊x⌋ = N := by
    obtain h | h | h | h := hn
    all_goals (simp at h; constructor)
    any_goals omega
    . suffices h :  (1^_) ≤ N ∧ N < ((_+1)^_) by exact hn_range₂ N _ h (by norm_num)
      norm_num; assumption
    . suffices h :  (2^_) ≤ N ∧ N < ((_+1)^_) by exact hn_range₂ N _ h (by norm_num)
      norm_num; assumption
    . suffices h :  (3^_) ≤ N ∧ N < ((_+1)^_) by exact hn_range₂ N _ h (by norm_num)
      norm_num; assumption
    . suffices h :  (4^_) ≤ N ∧ N < ((_+1)^_) by exact hn_range₂ N _ h (by norm_num)
      norm_num; assumption
  -- previous two fact implies target set is just [1, 2) ∪ [4, 9) ∪ [27, 64) ∪ [256, 625)
  have hs_eq : {N : ℕ | N < 1000 ∧ ∃ x : ℝ, x ^ ⌊x⌋ = N} = Set.Ico 1 2 ∪ Set.Ico 4 9 ∪ Set.Ico 27 64 ∪ Set.Ico 256 625 := by
    ext N
    constructor
    . rintro ⟨hN, ⟨x, hx⟩⟩
      have := hn_ranges₁ N x hN hx
      simp at this; simp
      omega
    . rintro hN
      simp
      have hN : N ∈ Set.Ico 1 2 ∨ N ∈ Set.Ico 4 9 ∨ N ∈ Set.Ico 27 64 ∨ N ∈ Set.Ico 256 625 := by
        simp; simp at hN
        omega
      exact hn_ranges₂ N hN
  -- now just add up the sizes to get 412
  have := Set.finite_Ico 1 2
  have := Set.finite_Ico 4 9
  have := Set.finite_Ico 256 625
  calc
    {N : ℕ | N < 1000 ∧ ∃ x : ℝ, x ^ ⌊x⌋ = N}.ncard = (Set.Ico 1 2 ∪ Set.Ico 4 9 ∪ Set.Ico 27 64 ∪ Set.Ico 256 625).ncard := by
      rw [hs_eq]
    _ = (Set.Ico 1 2).ncard + (Set.Ico 4 9).ncard + (Set.Ico 27 64).ncard + (Set.Ico 256 625).ncard := by
      repeat rw [Set.ncard_union_eq]
      all_goals (
        apply Set.disjoint_left.mpr
        intro n hn
        by_contra ht
        simp at hn; simp at ht
        omega
      )
    _ = Nat.card (Set.Ico 1 2) + Nat.card (Set.Ico 4 9) + Nat.card (Set.Ico 27 64) + Nat.card (Set.Ico 256 625) := by repeat rw [← Set.Nat.card_coe_set_eq]
    _ = 412 := by simp