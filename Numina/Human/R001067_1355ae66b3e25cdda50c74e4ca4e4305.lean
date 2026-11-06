import Mathlib

open Real Set
open scoped BigOperators

/- Let $p(x)=\sqrt{-x}$, and $q(x)=8x^2+10x-3$. The domain of $p(q(x))$ can be written in the form $a\le x \le b$. Find $b-a$. -/
theorem algebra_20271 {p q : ℝ → ℝ} {a b : ℝ}
  (_ : p = λ x => sqrt (-x)) (_ : q = λ x => 8 * x ^ 2 + 10 * x - 3) (h : {x : ℝ | -(8 * x ^ 2 + 10 * x - 3) ≥ 0} = (Icc a b)) :
  b - a = 7 / 4 := by
    /- 第一步：证明定义域是区间 [-3/2, 1/4] -/
    have h1 : {x : ℝ| -(8 * x ^ 2 + 10 * x - 3) ≥ 0} ⊆ (Icc (-3 / 2)  (1 / 4)):= by
      simp
      intro x hx
      simp at hx
      simp
      constructor
      . /- 证明左端点 x ≥ -3/2 -/
        by_contra H
        simp at H
        replace hx : (x + 5 / 8) ^ 2 ≤ 49 / 64:= by linarith
        replace H : x + 5 / 8 < - 7 / 8:= by linarith
        replace H : (x + 5 / 8) ^ 2 > 49 / 64:= by nlinarith only [H]
        linarith
      . /- 证明右端点 x ≤ 1/4 -/
        ring_nf
        by_contra H
        ring_nf at H
        replace hx : (x + 5 / 8) ^ 2 ≤ 49 / 64:= by linarith
        replace H : x + 5 / 8 > 7 / 8:= by linarith
        replace H : (x + 5 / 8) ^ 2 > 49 / 64:= by nlinarith only [H]
        linarith

    /- 第二步：证明 [-3/2, 1/4] 包含在定义域中 -/
    have h2 : (Icc (-3 / 2)  (1 / 4)) ⊆ {x : ℝ| -(8 * x ^ 2 + 10 * x - 3) ≥ 0}:= by
      simp
      intro x hx
      simp at hx
      simp
      rcases hx with ⟨hx1, hx2⟩
      ring_nf at hx2
      have h2 : (x + 5 / 8) ^ 2 ≤ 49 / 64:= by nlinarith only [hx1, hx2]
      linarith

    /- 第三步：由双向包含证明集合相等 -/
    have h3 : {x : ℝ| -(8 * x ^ 2 + 10 * x - 3) ≥ 0} = (Icc (-3 / 2)  (1 / 4)):= Eq.symm (Subset.antisymm h2 h1)
    clear h1 h2
    rw [h3] at h
    clear h3
    simp [Icc] at h

    /- 第四步：证明端点属于集合 -/
    have g1 : (-3 : ℝ) / 2 ∈ {x | -3 / 2 ≤ x ∧ x ≤ 4⁻¹}:= by
      simp
      linarith
    have g2 : (1 : ℝ) / 4 ∈ {x | -3 / 2 ≤ x ∧ x ≤ 4⁻¹}:= by
      simp
      linarith
    have g3 : (-3 : ℝ) / 2 ∈ {x | a ≤ x ∧ x ≤ b}:= by
      rw [←h]
      exact g1
    have g4 : (1 : ℝ) / 4 ∈ {x | a ≤ x ∧ x ≤ b}:= by
     rw [←h]
     exact g2

    /- 第五步：通过集合相等性得到端点关系 -/
    simp at g3
    simp at g4
    rcases g3 with ⟨h1, h2⟩
    rcases g4 with ⟨h3, h4⟩
    ring_nf at h3 h4
    have g5 : a ∈ {x | a ≤ x ∧ x ≤ b}:= by
      simp
      linarith
    have g6 : b ∈ {x | a ≤ x ∧ x ≤ b}:= by
      simp
      linarith
    have g7 : a ∈ {x | -3 / 2 ≤ x ∧ x ≤ 4⁻¹}:= by
      rw [h]
      exact g5
    have g8 : b ∈ {x | -3 / 2 ≤ x ∧ x ≤ 4⁻¹}:= by
      rw [h]
      exact g6
    simp at g7 g8
    rcases g7 with ⟨h5, h6⟩
    rcases g8 with ⟨ _, h8⟩
    clear g1 g2 g5 g6
    ring_nf at h6 h8
    /- 最后：计算 b-a = 7/4 -/
    linarith
