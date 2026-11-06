import Mathlib

/- Find the number of ordered triples $(x,y,z)$ of real numbers such that
\[x^4 + y^4 + z^4 - 4xyz = -1.\] -/
theorem algebra_18864 :
    {(x, y, z) : ℝ × ℝ × ℝ | x ^ 4 + y ^ 4 + z ^ 4 - 4 * x * y * z = -1}.ncard = 4 := by
    -- 第一步：证明所有满足方程的点 (x,y,z) 的每个分量的绝对值都等于1
    have h1 : ∀ n ∈ {(x, y, z) : ℝ × ℝ × ℝ | x ^ 4 + y ^ 4 + z ^ 4 - 4 * x * y * z = -1}, |n.1| = 1 ∧ |n.2.1| = 1 ∧ |n.2.2| = 1 := by
        intro n hn
        let ⟨x, y, z⟩ := n
        simp
        -- 将原方程转换为等价形式
        have h2 : x ^ 4 + y ^ 4 + z ^ 4 - 4 * x * y * z = -1:= hn
        clear hn
        replace h2 : x ^ 4 + y ^ 4 + z ^ 4 + 1 = 4 * x * y * z := by linarith
        replace h2 : |x ^ 4 + y ^ 4 + z ^ 4 + 1| = |4 * x * y * z|:= by rw [h2]

        -- 证明x^4, y^4, z^4都是非负的
        have hxyz : 0 ≤ x ^ 4 + y ^ 4 + z ^ 4 + 1:= by positivity

        -- 将等式转换为绝对值形式
        replace h2 : |x| ^ 4 + |y| ^ 4 + |z| ^ 4 + 1 = 4 * |x| * |y| * |z|:= by
            calc _ = |x ^ 4| + |y ^ 4| + |z ^ 4| + 1:= by rw [symm (abs_pow x 4), symm (abs_pow y 4), symm (abs_pow z 4)]
                 _ = x ^ 4 + y ^ 4 + z ^ 4 + 1:= by rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
                 _ = |x ^ 4 + y ^ 4 + z ^ 4 + 1|:= by rw [abs_of_nonneg hxyz]
                 _ = |4 * x * y * z|:= by rw [h2]
                 _ = 4 * |x| * |y| * |z|:= by rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by linarith)]

        -- 整理等式
        replace h2 : |x| ^ 4 + |y| ^ 4 + |z| ^ 4 + 1 - 4 * |x| * |y| * |z| = 0:= by linarith
        -- 证明|x| = 1
        have hx : (|x| ^ 2 - 1) ^ 2 + (|y| ^ 2 - |z| ^ 2) ^ 2 + 2 * (|x| - |y| * |z|) ^ 2 = 0:= by
            ring_nf
            linarith
        have h3 : (|x| ^ 2 - 1) ^ 2 ≥ 0:= by positivity
        have h4 : (|y| ^ 2 - |z| ^ 2) ^ 2 ≥ 0:= by positivity
        have h5 : 2 * (|x| - |y| * |z|) ^ 2 ≥ 0:= by positivity
        replace h3 : (|x| ^ 2 - 1) ^ 2 = 0:= by linarith
        replace h3 : |x| ^ 2 - 1 = 0:= pow_eq_zero h3
        replace h3 : (|x| - 1) * (|x| + 1) = 0:= by
            ring_nf
            linarith
        have h6 : |x| + 1 ≠ 0:= by positivity
        replace h3 : |x| - 1 = 0:= eq_zero_of_ne_zero_of_mul_right_eq_zero h6 h3
        have hx3 : |x| = 1:= by linarith
        clear hx h3 h4 h5 h6
        -- 类似地证明|y| = 1
        have hy : (|y| ^ 2 - 1) ^ 2 + (|x| ^ 2 - |z| ^ 2) ^ 2 + 2 * (|y| - |x| * |z|) ^ 2 = 0:= by
            ring_nf
            linarith
        have h3 : (|y| ^ 2 - 1) ^ 2 ≥ 0:= by positivity
        have h4 : (|x| ^ 2 - |z| ^ 2) ^ 2 ≥ 0:= by positivity
        have h5 : 2 * (|y| - |x| * |z|) ^ 2 ≥ 0:= by positivity
        replace h3 : (|y| ^ 2 - 1) ^ 2 = 0:= by linarith
        replace h3 : |y| ^ 2 - 1 = 0:= pow_eq_zero h3
        replace h3 : (|y| - 1) * (|y| + 1) = 0:= by
            ring_nf
            linarith
        have h6 : |y| + 1 ≠ 0:= by positivity
        replace h3 : |y| - 1 = 0:= eq_zero_of_ne_zero_of_mul_right_eq_zero h6 h3
        have hy3 : |y| = 1:= by linarith
        clear hy h3 h4 h5 h6

        -- 类似地证明|z| = 1
        have hz : (|z| ^ 2 - 1) ^ 2 + (|y| ^ 2 - |x| ^ 2) ^ 2 + 2 * (|z| - |y| * |x|) ^ 2 = 0:= by
            ring_nf
            linarith
        have h3 : (|z| ^ 2 - 1) ^ 2 ≥ 0:= by positivity
        have h4 : (|y| ^ 2 - |x| ^ 2) ^ 2 ≥ 0:= by positivity
        have h5 : 2 * (|z| - |y| * |x|) ^ 2 ≥ 0:= by positivity
        replace h3 : (|z| ^ 2 - 1) ^ 2 = 0:= by linarith
        replace h3 : |z| ^ 2 - 1 = 0:= pow_eq_zero h3
        replace h3 : (|z| - 1) * (|z| + 1) = 0:= by
            ring_nf
            linarith
        have h6 : |z| + 1 ≠ 0:= by positivity
        replace h3 : |z| - 1 = 0:= eq_zero_of_ne_zero_of_mul_right_eq_zero h6 h3
        have hz3 : |z| = 1:= by linarith
        clear h2 hz h3 h4 h5 h6
        constructor
        .
            exact hx3
        .
            constructor
            . exact hy3
            . exact hz3

    -- 第二步：证明所有满足方程的点都在给定的四个点集合中
    have h2 : ∀ n ∈ {(x, y, z) : ℝ × ℝ × ℝ | x ^ 4 + y ^ 4 + z ^ 4 - 4 * x * y * z = -1}, n ∈ {n| n = (1, 1, 1) ∨ n = (-1, -1, 1) ∨ n = (-1, 1, -1) ∨ n = (1, -1, -1)} := by
        intro n hn
        specialize h1 n hn
        simp at hn
        let ⟨x, y, z⟩ := n
        simp at h1 hn
        -- 由于每个分量的绝对值为1，所以每个分量只能是1或-1
        have hx : x = 1 ∨ x = -1:=eq_or_eq_neg_of_abs_eq h1.1
        have hy : y = 1 ∨ y = -1:=eq_or_eq_neg_of_abs_eq h1.2.1
        have hz : z = 1 ∨ z = -1:=eq_or_eq_neg_of_abs_eq h1.2.2
        simp
        -- 通过分类讨论，证明点必须是四个给定点之一
        rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
        all_goals
        simp [hx, hy, hz] at hn
        simp [hx, hy, hz]
        all_goals
        linarith
    -- 第三步：证明给定的四个点都满足原方程
    have h3 : ∀ n ∈ {n : ℝ × ℝ × ℝ | n = (1, 1, 1) ∨ n = (-1, -1, 1) ∨ n = (-1, 1, -1) ∨ n = (1, -1, -1)}, n ∈ {(x, y, z) : ℝ × ℝ × ℝ | x ^ 4 + y ^ 4 + z ^ 4 - 4 * x * y * z = -1}:= by
        intro n hn
        let ⟨x, y, z⟩ := n
        simp
        simp at hn
        rcases hn with h4 | h4 | h4 | h4
        all_goals
        have hx := h4.1
        have hy := h4.2.1
        have hz := h4.2.2
        simp [hx, hy, hz]
        norm_num

    -- 第四步：证明两个集合相等
    have h4 : {(x, y, z) : ℝ × ℝ × ℝ | x ^ 4 + y ^ 4 + z ^ 4 - 4 * x * y * z = -1} = {n | n = (1, 1, 1) ∨ n = (-1, -1, 1) ∨ n = (-1, 1, -1) ∨ n = (1, -1, -1)}:= by exact Set.Subset.antisymm h2 h3

    -- 最后一步：证明这四个点互不相同，因此集合基数为4
    rw [h4]
    clear h1 h2 h3 h4
    have h1 : ¬(1 : ℝ) = -1 := by linarith
    change Set.ncard {(1, 1, 1), (-1, -1, 1), (-1, 1, -1), (1, -1, -1)} = 4
    rw [show ({(1, 1, 1), (-1, -1, 1), (-1, 1, -1), (1, -1, -1)} : Set (ℝ × ℝ × ℝ)) = ({(1, 1, 1), (-1, -1, 1), (-1, 1, -1), (1, -1, -1)} : Finset (ℝ × ℝ × ℝ)) by simp]
    rw [Set.ncard_coe_Finset]
    rw [Finset.card_insert_of_not_mem]
    rw [Finset.card_insert_of_not_mem]
    rw [Finset.card_insert_of_not_mem]
    simp [h1]
    simp [h1]
    simp [h1]
    simp [h1]
    constructor
    .
        by_contra!
        injection this
        linarith

    .
        constructor
        .
            by_contra!
            injection this
            linarith
        .
            by_contra!
            injection this with h2 h3
            injection h3
            linarith
