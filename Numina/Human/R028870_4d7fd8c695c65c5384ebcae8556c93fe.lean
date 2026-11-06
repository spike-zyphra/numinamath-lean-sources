import Mathlib

/- Two numbers are independently selected from the set of positive integers less
than or equal to 5. What is the probability that the sum of the two numbers is
greater than their product? Express your answer as a common fraction. -/
theorem algebra_21248 :
    -- 目标：证明满足条件的数对数量除以25等于9/25
    (Set.ncard {(x, y): ℤ × ℤ | x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ x + y > x * y}) / 25 = 9 / 25 := by
    -- h1：证明满足条件的数对总数为9
    have h1 : Set.ncard {(x, y): ℤ × ℤ | x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ x + y > x * y} = 9 := by
        -- h2：证明所有满足条件的数对都在这9个特定数对中
        have h2 : ∀ n ∈ {(x, y): ℤ × ℤ | x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ x + y > x * y}, n ∈ {n | n = (1, 1) ∨ n = (1, 2) ∨ n = (1, 3) ∨ n = (1, 4) ∨ n = (1, 5) ∨ n = (2, 1) ∨ n = (3, 1) ∨ n = (4, 1) ∨ n = (5, 1)}:= by
            intro n hn
            let ⟨x, y⟩ := n
            simp at hn
            simp
            have hn1 := hn.1      -- x在1到5之间
            have hn2 := hn.2.1    -- y在1到5之间
            have hn3 := hn.2.2    -- x + y > x * y
            clear hn
            -- 代数变换：(x + y > x * y) ⟹ ((x-1)(y-1) < 1)
            replace hn3 : (x - 1) * (y - 1) < 1 := by nlinarith
            have hn4 : x - 1 ≥ 0 := by linarith
            have hn5 : y - 1 ≥ 0 := by linarith
            replace hn3 : (x - 1) * (y - 1) = 0 := by nlinarith
            -- 因为两个非负数的积为0，所以其中一个必须为0
            have hn6 : x - 1 = 0 ∨ y - 1 = 0 := Int.mul_eq_zero.mp hn3
            rcases hn6 with hn6 | hn6
            -- 分情况讨论：x=1的情况
            .
                replace hn6 : x = 1 := by linarith
                by_contra!
                have g1 := this.1
                have g2 := this.2.1
                have g3 := this.2.2.1
                have g4 := this.2.2.2.1
                have g5 := this.2.2.2.2.1
                clear this
                specialize g1 hn6
                specialize g2 hn6
                specialize g3 hn6
                specialize g4 hn6
                specialize g5 hn6
                have hnl:= hn2.1
                have hnr:= hn2.2
                omega
            -- 分情况讨论：y=1的情况
            .
                replace hn6 : y = 1 := by linarith
                by_contra!
                have h : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by omega
                rcases h with h | h | h | h | h
                -- 处理x从1到5的五种情况
                .
                    have g1 := this.1
                    have g2 := this.2.1
                    have g3 := this.2.2.1
                    have g4 := this.2.2.2.1
                    have g5 := this.2.2.2.2.1
                    clear this
                    specialize g1 h
                    specialize g2 h
                    specialize g3 h
                    specialize g4 h
                    specialize g5 h
                    omega
                .
                    have g := this.2.2.2.2.2.1
                    specialize g h
                    omega
                .
                    have g := this.2.2.2.2.2.2.1
                    specialize g h
                    omega
                .
                    have g := this.2.2.2.2.2.2.2.1
                    specialize g h
                    omega
                .
                    have g := this.2.2.2.2.2.2.2.2
                    specialize g h
                    omega
        -- h3：证明这9个特定数对都满足条件
        have h3 : ∀ n ∈ {n : ℤ × ℤ | n = (1, 1) ∨ n = (1, 2) ∨ n = (1, 3) ∨ n = (1, 4) ∨ n = (1, 5) ∨ n = (2, 1) ∨ n = (3, 1) ∨ n = (4, 1) ∨ n = (5, 1)}, n ∈ {(x, y): ℤ × ℤ | x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ x + y > x * y} := by
            intro n hn
            let ⟨x, y⟩ := n
            simp at hn
            simp
            rcases hn with hn | hn | hn | hn | hn | hn | hn | hn | hn
            all_goals
                have hn1 := hn.1
                have hn2 := hn.2
                rw[hn1, hn2]
                constructor
                .
                    constructor
                    all_goals omega
                .
                    constructor
                    .
                        constructor
                        all_goals omega
                    .
                        omega
        -- h4：证明两个集合相等（使用集合包含的反对称性）
        have h4 : {(x, y): ℤ × ℤ | x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ x + y > x * y} = {n | n = (1, 1) ∨ n = (1, 2) ∨ n = (1, 3) ∨ n = (1, 4) ∨ n = (1, 5) ∨ n = (2, 1) ∨ n = (3, 1) ∨ n = (4, 1) ∨ n = (5, 1)}:= by exact Set.Subset.antisymm h2 h3
        rw[h4]
        clear h2 h3 h4
        -- 计算集合的基数
        change Set.ncard {(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (3, 1), (4, 1), (5, 1)} = 9
        rw [show ({(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (3, 1), (4, 1), (5, 1)} : Set (ℤ × ℤ)) = ({(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (3, 1), (4, 1), (5, 1)} : Finset (ℤ × ℤ)) by simp]
        rw [Set.ncard_coe_Finset]
        -- 证明所有数对都不相同
        repeat rw [Finset.card_insert_of_not_mem]
        simp
        all_goals
            by_contra!
            simp at this
        rcases this with h | h | h | h | h | h | h | h
        all_goals
            injection h
            linarith
    -- 使用h1完成最终证明
    rw[h1]
