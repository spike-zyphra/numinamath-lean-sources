import Mathlib

open Real Set
open scoped BigOperators

/- Find the domain of the function $f(x)=\sqrt{\sqrt{x^2-16}-3}$. -/
theorem algebra_20824 {f : ℝ → ℝ} (hf : f = λ x => √(√(x ^ 2 - 16) - 3)) :
    /- 定义域可以表示为满足两个条件的实数集合：
       1. x^2-16 ≥ 0 （保证第一个根号下是非负数）
       2. √(x^2-16)-3 ≥ 0 （保证第二个根号下是非负数）
       这个集合等于 (-∞,-5]∪[5,+∞) -/
    {x : ℝ | x ^ 2 - 16 ≥ 0 ∧ √(x ^ 2 - 16) - 3 ≥ 0} = (Set.Iic (-5 : ℝ)) ∪ Set.Ici 5:= by
        clear f hf
        /- 第一部分：证明定义域是(-∞,-5]∪[5,+∞)的子集 -/
        have h1 : {x : ℝ | x ^ 2 - 16 ≥ 0 ∧ √(x ^ 2 - 16) - 3 ≥ 0} ⊆ ((Set.Iic (-5 : ℝ)) ∪ Set.Ici 5):= by
            simp
            intro x hx
            simp
            simp at hx
            rcases hx with ⟨h1, h2⟩
            /- 从条件中提取 x^2-16 ≥ 0 -/
            replace h1 : x ^ 2 - 16 ≥ 0:= by linarith
            /- 从 √(x^2-16)-3 ≥ 0 推导出 (√(x^2-16))^2 ≥ 9 -/
            replace h2 : (√(x ^ 2 - 16)) ^ 2 ≥ 9:= by nlinarith only [h1, h2]
            /- 利用平方根的性质简化表达式 -/
            rw [show ((√(x ^ 2 - 16)) ^ 2 = x ^ 2 - 16) by exact sq_sqrt h1] at h2
            clear h1
            /- 转化为因式分解形式 (x-5)(x+5) ≥ 0 -/
            replace h2 : (x - 5) * (x + 5) ≥ 0:= by linarith
            /- 使用反证法证明 x ≤ -5 或 x ≥ 5 -/
            by_contra H
            simp at H
            rcases H with ⟨H1, H2⟩
            replace H1 : x + 5 > 0:= by linarith
            replace H2 : x - 5 < 0:= by linarith
            nlinarith only [h2, H1, H2]

        /- 第二部分：证明(-∞,-5]∪[5,+∞)是定义域的子集 -/
        have h2 : ((Set.Iic (-5 : ℝ)) ∪ Set.Ici 5) ⊆ {x : ℝ | x ^ 2 - 16 ≥ 0 ∧ √(x ^ 2 - 16) - 3 ≥ 0}:= by
            simp
            constructor
            /- 证明 x ≤ -5 的情况 -/
            .
                intro x hx
                simp at hx
                simp
                constructor
                /- 证明 x^2-16 ≥ 0 -/
                .
                    nlinarith only [hx]
                /- 证明 √(x^2-16)-3 ≥ 0 -/
                .
                    have h2 : x ^ 2 - 16 ≥ 9:= by nlinarith only [hx]
                    rw [←show √(3 ^ 2) = (3 : ℝ) by refine sqrt_sq (by linarith)]
                    rw [show (9 : ℝ) = 3 ^ 2 by norm_num] at h2
                    change √(x ^ 2 - 16) ≥ √(3 ^ 2)
                    exact sqrt_le_sqrt h2
            /- 证明 x ≥ 5 的情况 -/
            .
                intro x hx
                simp at hx
                simp
                constructor
                /- 证明 x^2-16 ≥ 0 -/
                .
                    nlinarith only [hx]
                /- 证明 √(x^2-16)-3 ≥ 0 -/
                .
                    have h2 : x ^ 2 - 16 ≥ 9:= by nlinarith only [hx]
                    rw [←show √(3 ^ 2) = (3 : ℝ) by refine sqrt_sq (by linarith)]
                    rw [show (9 : ℝ) = 3 ^ 2 by norm_num] at h2
                    change √(x ^ 2 - 16) ≥ √(3 ^ 2)
                    exact sqrt_le_sqrt h2

        /- 最后，利用集合包含的反对称性证明两个集合相等 -/
        have h3 : {x : ℝ | x ^ 2 - 16 ≥ 0 ∧ √(x ^ 2 - 16) - 3 ≥ 0} = ((Set.Iic (-5 : ℝ)) ∪ Set.Ici 5):= Subset.antisymm h1 h2
        exact h3
