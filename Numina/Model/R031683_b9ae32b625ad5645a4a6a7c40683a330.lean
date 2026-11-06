import Mathlib

theorem algebra_260569_correct (a1 r1 r2 r3 d q3 : ℝ)
    (h₁ : q3 = 2) -- 首项构成的等比数列的公比 
    (h₂ : r2 = r1 + d) -- 公比构成的等差数列 
    (h₃ : r3 = r2 + d) -- 公比构成的等差数列 
    (h₄ : d = 1) -- 公比构成的等差数列的公差 
    (h₅ : a1 * r1 + (a1 * q3) * r2 + (a1 * q3 * q3) * r3 = 24) -- 第二项之和 
    (h₆ : (a1 * q3 * q3) + (a1 * q3 * q3) * r3 + (a1 * q3 * q3) * r3 * r3 = 84) -- 第三个数列的前三项之和 
    : {(a1, r1, r2, r3) | a1 * r1 + (a1 * q3) * r2 + (a1 * q3 * q3) * r3 = 24 ∧ 
                         (a1 * q3 * q3) + (a1 * q3 * q3) * r3 + (a1 * q3 * q3) * r3 * r3 = 84 ∧
                         q3 = 2 ∧ r2 = r1 + d ∧ r3 = r2 + d ∧ d = 1} = 
      {(1, 2, 3, 4), (192/31, -7/8, 1/8, 9/8)} := by
  ext ⟨a1, r1, r2, r3⟩
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · -- Forward direction: if the equations hold, then the point is in the set
    intro h
    rcases h with ⟨h5, h6, hq3, hr2, hr3, hd⟩
    have h2 : r2 = r1 + 1 := by
      rw [h₄] at h₂
      nlinarith
    have h3 : r3 = r1 + 2 := by
      rw [h₄] at h₃
      nlinarith [h₂]
    have hq3' : q3 = 2 := by linarith [hq3]
    have eq1 : a1 * r1 + (a1 * 2) * (r1 + 1) + (a1 * 4) * (r1 + 2) = 24 := by
      rw [hq3'] at h5
      have h2' : r2 = r1 + 1 := by
        nlinarith [h₂, h₄]
      have h3' : r3 = r1 + 2 := by
        nlinarith [h₃, h₂, h₄]
      simp only [h2', h3'] at h5
      nlinarith
    have eq2 : (a1 * 4) + (a1 * 4) * (r1 + 2) + (a1 * 4) * (r1 + 2)^2 = 84 := by 
      rw [hq3'] at h6
      have h3' : r3 = r1 + 2 := by
        nlinarith [h₃, h₂, h₄]
      simp only [h3'] at h6
      nlinarith
    -- Solve the quadratic for r1
    have hr1_eq : (r1 - 2) * (8 * r1 + 7) = 0 := by 
      nlinarith [sq_nonneg (a1), sq_nonneg (r1 - 2), sq_nonneg (r1 + 7/8)]
    cases' (mul_eq_zero.1 hr1_eq) with hr12 hr1neg78
    · -- Case 1: r1 = 2. Then a1 = 1.
      have hr12' : r1 = 2 := by linarith
      have ha12 : a1 = 1 := by
        rw [hr12'] at eq1
        linarith
      -- Now we show that (a1, r1, r2, r3) equals the first pair in the boxed answer
      have h10 : a1 = 1 := by linarith [ha12]
      have h11 : r1 = 2 := by linarith [hr12']
      have h12 : r2 = 3 := by
        nlinarith [h2, hr12']
      have h13 : r3 = 4 := by
        nlinarith [h3, hr12']
      simp [h10, h11, h12, h13]
      <;> norm_num 
      <;> tauto 
    · -- Case 2: 8 * r1 + 7 = 0, so r1 = -7/8. Then a1 = 192/31.
      have hr1neg78' : r1 = -7 / 8 := by
        linarith
      have ha1neg78 : a1 = 192 / 31 := by
        rw [hr1neg78'] at eq1
        linarith
      -- Now we show that (a1, r1, r2, r3) equals the second pair in the boxed answer
      have h14 : a1 = 192 / 31 := by linarith [ha1neg78]
      have h15 : r1 = -7 / 8 := by linarith [hr1neg78']
      have h16 : r2 = 1 / 8 := by
        nlinarith [h2, hr1neg78']
      have h17 : r3 = 9 / 8 := by
        nlinarith [h3, hr1neg78']
      simp [h14, h15, h16, h17]
      <;> norm_num 
      <;> tauto 
  · -- Backward direction: if the point is in the set, then the equations hold
    rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
    · -- Check first point
      constructor
      · -- Equation 1: a1 * r1 + (a1 * q3) * r2 + (a1 * q3 * q3) * r3 = 24
        norm_num [h₁]
      constructor
      · -- Equation 2: (a1 * q3 * q3) + (a1 * q3 * q3) * r3 + (a1 * q3 * q3) * r3 * r3 = 84
        norm_num [h₁]
      constructor
      · -- q3 = 2
        exact h₁
      constructor
      · -- r2 = r1 + d
        norm_num [h₂, h₄]
      constructor
      · -- r3 = r2 + d
        norm_num [h₃, h₂, h₄]
      · -- d = 1
        exact h₄
    · -- Check second point
      constructor
      · -- Equation 1: a1 * r1 + (a1 * q3) * r2 + (a1 * q3 * q3) * r3 = 24
        norm_num [h₁]
      constructor
      · -- Equation 2: (a1 * q3 * q3) + (a1 * q3 * q3) * r3 + (a1 * q3 * q3) * r3 * r3 = 84
        norm_num [h₁]
      constructor
      · -- q3 = 2
        exact h₁
      constructor
      · -- r2 = r1 + d
        norm_num [h₂, h₄]
      constructor
      · -- r3 = r2 + d
        norm_num [h₃, h₂, h₄]
      · -- d = 1
        exact h₄