import Mathlib

open Set Nat Finset BigOperators

def floor_half (M : ℕ) : ℕ := M / 2  -- 自然数除法自动向下取整

-- 主定理 : 奇元素比例等于 (floor_half M / M) ^ 2
theorem odd_fraction (M : ℕ) (hM : M > 0) :
    (∑ i ∈ range M, ∑ j ∈ range M, if Odd (i * j) then 1 else 0 : ℚ) / (M * M : ℚ) = 
    (floor_half M : ℚ) / M * ((floor_half M : ℚ) / M) := by

let inner_eq (i M : ℕ) : ℚ := (∑ j ∈ range M, if Odd (i * j) then 1 else 0 : ℚ) 
have count_odds_eq_floor_half {M} : # ({x ∈ range M | Odd x}) = floor_half M := by
  rw [floor_half]
  -- 对 M 做归纳
  induction M with
  -- M = 0
  | zero =>
    trivial
  -- M → M + 1
  | succ M ih => 
    -- 分解为 range M ∪ {M}
    rw [range_succ, Finset.insert_eq, filter_union, filter_singleton]
    
    -- 根据 M 的奇偶性分类讨论
    cases' mod_two_eq_zero_or_one M with h_even h_odd
    -- 情况 1 : M 为偶数
    · have even_M : Even M := even_iff.2 h_even
      -- M 为偶数时不添加奇数
      rw [if_neg (by simp [even_M]), Finset.empty_union]
      -- 代数化简 : (M + 1) / 2 = M / 2
      · rw [ih]
        rcases even_M with ⟨k, rfl⟩
        have add_eq : k + k = 2 * k := by ring
        rw [add_eq]
        rw [Nat.mul_div_right, add_comm]
        rw [Nat.add_mul_div_left]
        norm_num
        · linarith
        · linarith

    -- 情况 2 : M 为奇数
    · have odd_M : Odd M := odd_iff.2 h_odd
      -- M 为奇数时添加基数 + 1
      rw [if_pos odd_M]
      rcases odd_M with ⟨k, rfl⟩
      have h_disjoint : Disjoint {2 * k + 1} (Finset.range (2 * k + 1)) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext x
        constructor
        · intro h
          have h_and := Iff.mp (Finset.mem_inter (α := ℕ)) h
          have h_singleton : x ∈ ({2 * k + 1} : Finset ℕ) := h_and.left
          have h_range : x ∈ range (2 * k + 1) := h_and.right
          rw [Finset.mem_range] at h_range
          rw [Finset.mem_singleton] at h_singleton
          rw [h_singleton] at h_range
          apply lt_irrefl at h_range
          trivial
        · intro h
          trivial
      rw [card_union_of_disjoint, Finset.card_singleton, ih]
      -- 证明 (2 * k + 2) / 2 = k + 1
      ring_nf
      rw [Nat.add_mul_div_right]
      rw [Nat.add_mul_div_right]
      norm_num
      · linarith
      · linarith
      have h : Disjoint {2 * k + 1} ({x ∈ Finset.range (2 * k + 1) | Odd x}) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext a
        constructor
        · intro h1
          have h_and := Iff.mp (Finset.mem_inter (α := ℕ)) h1
          have h_singleton : a ∈ ({2 * k + 1} : Finset ℕ) := h_and.left
          have h_range : a ∈ {x ∈ Finset.range (2 * k + 1) | Odd x} := h_and.right
          simp only [Finset.mem_filter, Finset.mem_range] at h_range
          rw [Finset.mem_singleton] at h_singleton
          have h_lt := h_range.left 
          rw [h_singleton] at h_lt
          apply lt_irrefl at h_lt
          trivial
        · intro h2
          trivial
      exact h
        
have odd_mul_iff (i j : ℕ) : Odd (i * j) ↔ Odd i ∧ Odd j := by
  exact Nat.odd_mul -- 计算内层求和 

have inner_eq_floor_half (i M : ℕ) : (inner_eq i M) = if Odd i then floor_half M else 0 := by
  -- 根据 i 的奇偶性分情况讨论
  rcases (em (Odd i)) with h_i_odd | h_i_even
  -- 情况 1 : i 为奇数 → 内层求和 = 奇数 j 的数量
  · rw [if_pos h_i_odd]
    simp_rw [inner_eq, odd_mul_iff, h_i_odd]
    simp
    rw [count_odds_eq_floor_half]
  -- 情况 2 : i为偶数
  · rw [if_neg h_i_even]
    simp_rw [inner_eq, odd_mul_iff, h_i_even]
    simp

  -- 步骤 1 : 计算满足条件的元素对数
have h_odd_entries : 
      (∑ i ∈ range M, ∑ j ∈ range M, if Odd (i * j) then 1 else 0 : ℚ) = 
      (floor_half M : ℚ) * (floor_half M : ℚ) := by
    -- 先对内层求和
    have h_sum_eq : (∑ i ∈ range M, ∑ j ∈ range M, if Odd (i * j) then 1 else 0) = 
                  ∑ i ∈ range M, inner_eq i M := by
      apply sum_congr rfl
      intro i hi
      simp [inner_eq]
    rw [h_sum_eq]
    have h_cast : (∑ i ∈ range M, inner_eq i M : ℚ) = 
                ∑ i ∈ range M, (if Odd i then ↑(floor_half M) else 0) := by
      apply sum_congr rfl
      intro i hi
      rw [inner_eq_floor_half i M]
      split
      · simp [*] 
      · simp 
    rw [h_cast]
    rw [sum_ite]
    simp only [sum_const, nsmul_eq_mul, card_range, mul_zero, add_zero]
    rw [count_odds_eq_floor_half]
  -- 步骤 2 : 代数化简
rw [h_odd_entries]
field_simp [hM, pow_two]