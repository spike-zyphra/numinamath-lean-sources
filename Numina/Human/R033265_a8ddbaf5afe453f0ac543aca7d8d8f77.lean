import Mathlib

/- Suppose that we roll two fair 6-sided dice.  What is the probability that the two numbers rolled sum to 4? -/
theorem algebra_21495 :
    (↑({x : ℤ × ℤ | (x.1 ∈ Int.range 1 7) ∧ (x.2 ∈ Int.range 1 7) ∧ (x.1 + x.2 = 4)}.ncard) : ℝ) / (6 * 6) = 1 / 12 := by
    -- h1证明：满足条件的点对集合是{(1,3), (2,2), (3,1)}的子集
    have h1 : {x : ℤ × ℤ | (x.1 ∈ Int.range 1 7) ∧ (x.2 ∈ Int.range 1 7) ∧ (x.1 + x.2 = 4)} ⊆ {(1, 3), (2, 2), (3, 1)}:= by
        intro x hx
        simp
        simp at hx
        let ⟨a, b⟩:= x
        simp
        simp at hx
        rcases hx with ⟨h1, h2, hsum⟩
        simp [Int.mem_range_iff] at h1 h2
        rcases h2 with ⟨h3, h4⟩
        rcases h1 with ⟨h1, _⟩
        have _ : a ≤ 3:= by omega
        -- 分类讨论：a ≤ 1 或 a > 1
        have g1 : a ≤ 1 ∨ a > 1:= by exact Int.le_or_lt a 1
        rcases g1 with g1 | g1
        . -- 情况1：当a ≤ 1时
            replace g1 : a = 1:= by omega
            have g2 : b = 3:= by omega
            left
            exact ⟨g1, g2⟩
        . -- 情况2：当a > 1时，继续分类讨论
            have g2 : a ≤ 2 ∨ a > 2:= by exact Int.le_or_lt a 2
            rcases g2 with g2 | g2
            . -- 子情况1：当1 < a ≤ 2时
                replace g2 : a = 2:= by omega
                have g3 : b = 2:= by omega
                right
                left
                exact ⟨g2, g3⟩
            . -- 子情况2：当a > 2时
                replace g2 : a = 3:= by omega
                have g3 : b = 1:= by omega
                right
                right
                exact ⟨g2, g3⟩

    -- h2证明：{(1,3), (2,2), (3,1)}是满足条件的点对集合的子集
    have h2 : {(1, 3), (2, 2), (3, 1)} ⊆ {x : ℤ × ℤ | (x.1 ∈ Int.range 1 7) ∧ (x.2 ∈ Int.range 1 7) ∧ (x.1 + x.2 = 4)}:= by
        intro x hx
        simp
        simp at hx
        simp [Int.mem_range_iff]
        rcases hx with hx | hx | hx
        all_goals
        rw [hx]
        simp

    -- h3利用集合的反对称性证明两个集合相等
    have h3 : {x : ℤ × ℤ | (x.1 ∈ Int.range 1 7) ∧ (x.2 ∈ Int.range 1 7) ∧ (x.1 + x.2 = 4)} = {(1, 3), (2, 2), (3, 1)}:= Set.Subset.antisymm h1 h2
    clear h1 h2
    rw [h3]
    clear h3

    -- h1证明：满足条件的点对集合的基数为3
    have h1 : ({(1, 3), (2, 2), (3, 1)} : Set (ℤ × ℤ)).ncard = 3:= by
        rw [show ({(1, 3), (2, 2), (3, 1)} : Set (ℤ × ℤ)) = ({(1, 3), (2, 2), (3, 1)} : Finset (ℤ × ℤ)) by simp]
        simp
    rw [h1]
    -- 最后计算概率：3/(6*6) = 1/12
    norm_num
