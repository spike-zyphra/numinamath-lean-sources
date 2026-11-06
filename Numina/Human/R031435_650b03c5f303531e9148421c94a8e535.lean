import Mathlib


/- Find all positive integers $a$ and $b$ such that

$$
\frac{a^{2}+b}{b^{2}-a} \text { and } \frac{b^{2}+a}{a^{2}-b}
$$

are both integers. -/
theorem number_theory_607115 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
  (hab1: b^2-a ≠ 0) (hab2: a^2-b ≠ 0):
    ( (∃ k : ℤ, (a^2 + b:ℚ) / (b^2 - a) = k) ∧ (∃ m : ℤ, (b^2 + a:ℚ) / (a^2 - b) = m) ) ↔
    ( (a = 2 ∧ b = 2) ∨ (a = 3 ∧ b = 3) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨
      (a = 2 ∧ b = 1) ∨ (a = 3 ∧ b = 2) ) := by

  -- we may suppose a ≤ b
  wlog aleb: a ≤ b
  · push_neg at aleb
    specialize this b a hb ha hab2 hab1 (le_of_lt aleb)
    constructor
    · intro h
      replace := this.mp ⟨h.right, h.left⟩
      clear * - this
      tauto
    · intro h
      rw [and_comm]
      refine this.mpr ?_
      clear * - h
      tauto

  -- then b^2-a ≥ 0
  have h3: b^2 - a ≥ 0 := by
    linarith only [aleb, Int.le_self_pow_two b]

  -- if a^2+b / b^2-a is integer, must have a^2+b ≥ b^2-a
  replace h3 (h: ∃ k : ℤ, (a^2 + b:ℚ) / (b^2 - a) = k):
    a^2+b ≥ b^2-a := by
    apply Int.le_of_dvd (by linarith only [sq_nonneg a, hb]) ?_
    rcases h with ⟨k,hk⟩
    use k
    qify at hab1 ⊢
    rw [← hk]
    field_simp [hab1]

  -- rearrange the inequality, (a+b)(a-b+1) ≥ 0, or, a ≥ b-1
  replace h3 (h: ∃ k : ℤ, (a^2 + b:ℚ) / (b^2 - a) = k): a ≥ b-1 := by
    specialize h3 h
    replace h3: (a+b)*(a-b+1) ≥ 0 := by linarith only [h3]
    replace h3: a-b+1 ≥ 0 := by
      apply nonneg_of_mul_nonneg_right h3 ?_
      linarith only [ha, hb]
    linarith only [h3]

  constructor

  · rintro ⟨h1, h2⟩
    -- for a ≥ b-1 and a ≤ b, a can only be b or b-1
    obtain (hab | hab): a = b ∨ a = b-1 := by
      specialize h3 h1
      omega

    · -- case a=b
      simp only [← hab] at hab1
      qify at hab1
      have hnz: a-(1:ℚ) ≠ 0 := by
        by_contra!
        have: a = (1:ℚ) := by linarith only [this]
        simp [this] at hab1
      -- substitute, (a^2+a)/(a^2-a) = 1 + 2/(a-1) is integer
      have h4: (a^2+b:ℚ) / (b^2-a) = 1 + 2/(a-1) := by
        simp only [← hab]
        field_simp [hab1, hnz]
        ring
      rw [h4] at h1
      -- for 2/(a-1) be integer, a can only be 2 or 3
      obtain (aeq | aeq): a = 2 ∨ a = 3 := by
        have: a-1 ∣ 2 := by
          rcases h1 with ⟨k,hk⟩
          use (k-1)
          qify
          rw [← hk]
          simp only [add_sub_cancel_left, mul_div_cancel₀ 2 hnz]
        replace := Int.le_of_dvd (by norm_num) this
        replace: a ≤ 3 := by linarith only [this]
        clear * - ha this hnz
        norm_cast at hnz
        decide +revert
      -- since a=b, b is also determined.
      all_goals simp [← hab, aeq]

    · -- case a = b-1
      replace hab: b = a+1 := by linarith only [hab]
      simp only [hab] at hab2
      qify at hab2
      have hab2': a^2 - (a:ℚ) - 1 ≠ 0 := by
        rwa [sub_sub]
      -- substitute, (b^2+a)/(a^2-b) = 1 + (4a+2)/(a^2-a-1)
      have h4: (b^2+a:ℚ) / (a^2-b) = 1 + (4*a+2)/(a^2-a-1) := by
        simp only [hab]
        push_cast
        field_simp [hab2, hab2']
        ring
      rw [h4] at h2
      -- then a^2-a-1 ≤ 4a+2, since (4a+2)/(a^2-a-1) is integer.
      have hdvd: a^2-a-1 ∣ 4*a+2 := by
        rcases h2 with ⟨m,hm⟩
        use (m-1)
        qify
        rw [← hm, add_sub_cancel_left]
        field_simp [hab2']
      have h5: a^2-a-1 ≤ 4*a+2 := by
        exact Int.le_of_dvd (by linarith only [ha]) hdvd
      -- solve thie inequality, a^2-5a-3 ≤ 0, a ≤ 5.
      replace h5: a*(a-5) ≤ 3 := by linarith only [h5]
      replace h5: a ≤ 5 := by
        by_contra!
        replace: a-5 ≥ 1 := by
          exact Int.le_sub_right_of_add_le this
        have h6: a*(a-5) ≥ a := by
          exact (le_mul_iff_one_le_right ha).mpr this
        replace h6 := le_trans h6 h5
        linarith only [this, h6]
      -- try a = 1,2,3,4,5, and we find a=2,a=3 are the only possible solution.
      simp only [hab]
      clear * - ha h5 hdvd
      revert hdvd
      decide +revert


  · -- verification
    rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    all_goals
      clear * -
      apply And.intro <;> norm_num <;> aesop