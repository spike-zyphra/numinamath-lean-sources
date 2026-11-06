import Mathlib

/- What is the sum of all possible solutions of $\frac{9x}{13}+\frac{13}{9x}=\frac{250}{117x}$? -/
theorem algebra_20519 : ∑ᶠ x ∈ {x : ℝ | x ≠ 0 ∧ (9 * x / 13 + 13 / (9 * x) = 250 / (117 * x))}, x = 0:= by
  -- 第一步：证明所有解都在集合 {1, -1} 中
  have h1 : {x : ℝ | x ≠ 0 ∧ (9 * x / 13 + 13 / (9 * x) = 250 / (117 * x))} ⊆ {1, -1}:= by
    intro x hx
    simp at hx
    rcases hx with ⟨hx, h⟩
    simp
    -- 通过 field_simp 化简分式
    field_simp at h
    norm_num at h
    ring_nf at h
    -- 得到 x * (x^2 - 1) = 0
    replace h : x * (x ^ 2 - 1) = 0:= by linarith
    -- 由 x ≠ 0 得到 x^2 - 1 = 0
    replace h : x ^ 2 - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero hx h
    -- 因式分解得到 (x - 1)(x + 1) = 0
    replace h : (x - 1) * (x + 1) = 0:= by linarith
    -- 由乘积为零得到 x = 1 或 x = -1
    replace h : x - 1 = 0 ∨ x + 1 = 0:= by exact mul_eq_zero.mp h
    rcases h with h | h
    .
      left
      linarith
    .
      right
      linarith

  -- 第二步：证明 {1, -1} 中的每个元素都是解
  have h2 : {1, -1} ⊆ {x : ℝ | x ≠ 0 ∧ (9 * x / 13 + 13 / (9 * x) = 250 / (117 * x))}:= by
    intro x hx
    simp at hx
    simp
    rcases hx with hx | hx
    .
      constructor
      all_goals
      rw [hx]
      norm_num
    .
      constructor
      all_goals
      rw [hx]
      norm_num

  -- 第三步：由双向包含证明两个集合相等
  have h3 : {x : ℝ | x ≠ 0 ∧ (9 * x / 13 + 13 / (9 * x) = 250 / (117 * x))} = {1, -1}:= Set.Subset.antisymm h1 h2
  clear h1 h2
  rw [h3]

  -- 定义恒等函数 f(x) = x
  let f : ℝ → ℝ := (fun x => x)
  have hf : f = (fun x => x):= by rfl

  -- 使用 finsum_mem_finset_eq_sum 将有限和转换为集合上的求和
  have g := finsum_mem_finset_eq_sum f ({1, -1} : Finset ℝ)
  simp only [hf] at g
  change ∑ᶠ (i : ℝ) (_ : i ∈ {1, -1}), i = 0
  simp at g
  simp
  rw [g]

  -- 证明 1 不在集合 {-1} 中
  have h1 : (1 : ℝ) ∉ ({-1} : Finset ℝ):= by
    by_contra!
    simp at this
    linarith

  -- 最后计算和：1 + (-1) = 0
  rw [Finset.sum_insert h1]
  simp
