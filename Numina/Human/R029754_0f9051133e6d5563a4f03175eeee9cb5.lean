import Mathlib
open Real Set
/- The height (in meters) of a shot cannonball follows a trajectory given by $h(t) = -4.9t^2 + 14t - 0.4$ at time $t$ (in seconds). As an improper fraction, for how long is the cannonball above a height of $6$ meters? -/
theorem algebra_19296 (h : ℝ → ℝ) (a b : ℝ) (h_def : h = fun t => -4.9 * t ^ 2 + 14 * t - 0.4) : ∃ a b : ℝ, {t : ℝ | h t ≥ 6} = (Icc a b) ∧ b - a = 12 / 7:= by
    -- 证明集合 {t | h(t) ≥ 6} 被包含在区间 [4/7, 16/7] 中
    have h2 : {t : ℝ | h t ≥ 6} ⊆ (Icc (4 / 7)  (16 / 7)):= by
        -- 展开函数定义
        simp [h_def]  
        intro t ht
        simp at ht
        simp
        -- 将不等式规范化
        ring_nf at ht 
        -- 转化为二次函数的根之间的关系
        replace ht : (t - 4 / 7) * (t - 16 / 7) ≤ 0:= by linarith  
        constructor
        all_goals
        -- 反证法
        by_contra!  
        have H : (t - 4 / 7) * (t - 16 / 7) > 0:= by nlinarith only [this]
        linarith

    -- 证明区间 [4/7, 16/7] 被包含在集合 {t | h(t) ≥ 6} 中
    have h3 : (Icc (4 / 7)  (16 / 7)) ⊆ {t : ℝ | h t ≥ 6}:= by
        simp [h_def]
        intro t ht
        simp
        simp at ht
        -- 分解区间条件
        rcases ht with ⟨ht1, ht2⟩  
        ring_nf
        nlinarith only [ht1, ht2]
    use (4 / 7), (16 / 7)
    constructor
    .
        exact Eq.symm (Subset.antisymm h3 h2)
    .
        linarith
