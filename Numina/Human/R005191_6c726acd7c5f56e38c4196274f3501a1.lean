import Mathlib

/- Prove that for each real number $r>2$, there are exactly two or three positive real numbers $x$ satisfying the equation $x^{2}=r\lfloor x\rfloor$.
Note: $\lfloor x\rfloor$ denotes the largest integer less than or equal to $x$ -/
theorem algebra_606157 (r : ℝ) (hr : r > 2) :
    Set.ncard {x : ℝ | 0 < x ∧ x ^ 2 = r * ⌊x⌋} = 2 ∨
    Set.ncard {x : ℝ | 0 < x ∧ x ^ 2 = r * ⌊x⌋} = 3 := by
    -- Let $r&gt;2$ be a real number. Let $x$ be a positive real number such that $x^{2}=r\lfloor x\rfloor$ with $\lfloor x\rfloor=k$.
    have h1 : ∀ x ∈ {x : ℝ | 0 < x ∧ x ^ 2 = r * ⌊x⌋} , r-3 < ⌊x⌋ ∧ ⌊x⌋ ≤ r := by
      intro x hx ;simp at hx
      let k := ⌊x⌋
      have hk : x ^ 2 = r * k := hx.right
      -- Since $x&gt;0$ and $x^{2}=r k$, we also have $k&gt;0$.
      have hk' : k > 0 := by
        have : r * k > 0 := by nlinarith
        apply mul_pos_iff.mp at this
        rcases this with ⟨hr, hk⟩
        simp at hk ;exact hk
        linarith
    -- From $k \leq x&lt;k+1$, we get $k^{2} \leq x^{2}=r k &lt; k^{2}+2 k+1 \leq k^{2}+3 k$, hence $k \leq r &lt; k+3$, or $r-3 &lt; k \leq r$.
      have h2 : k ≤ x ∧ x < k + 1 := by
        exact Int.floor_eq_iff.mp rfl
      have h3 : k ^ 2 ≤ r * k := by
        rw [← hk] ;refine (sq_le_sq₀ (by simp ;linarith) (by linarith)).mpr h2.1
      have h4 : r * k < k ^ 2 + 3 * k := by
        rw [← hk]
        have h5 : x ^ 2 < (k + 1) ^ 2 := by
          refine (sq_lt_sq₀ (by linarith) (by linarith)).mpr h2.2
        have h6 : (↑k + 1 :ℝ) ^ 2 ≤  ↑k ^ 2 + 3 * ↑k := by
          ring_nf ;simp
          have : (↑k:ℝ) * 3 = ↑k + ↑k * 2 := by ring
          rw [this] ;simp ;exact Int.cast_one_le_of_pos hk'
        linarith
      constructor
      · rw [pow_two,← add_mul] at h4
        refine sub_right_lt_of_lt_add ?_
        apply (mul_lt_mul_iff_of_pos_right (by linarith)).mp at h4
        exact h4
      · rw [pow_two] at h3
        apply (mul_le_mul_iff_of_pos_right (by linarith)).mp at h3
        exact h3
    -- There are at most three positive integers in the interval $(r-3, r]$.
    -- Consequently, there are at most three positive solutions to the given equation.
    have hsub : {x | 0 < x ∧ x ^ 2 = r * ↑⌊x⌋} ⊆ {√ (r * ⌊r⌋),√ (r * (⌊r⌋-1)),√ (r * (⌊r⌋-2))} := by
      have : {x | 0 < x ∧ x ^ 2 = r * ↑⌊x⌋} ⊆ {x | x = √ (r * ⌊x⌋) ∧ r - 3 < ⌊x⌋ ∧ ⌊x⌋ ≤ r} := by
        intro x hx
        have : r - 3 < ↑⌊x⌋ ∧ ↑⌊x⌋ ≤ r := h1 x hx
        simp at hx
        simp [hx,this] ;rw [← hx.right] ;refine Eq.symm (Real.sqrt_sq (by linarith))
      have this' : {x | x = √ (r * ⌊x⌋) ∧ r - 3 < ⌊x⌋ ∧ ⌊x⌋ ≤ r} ⊆ {√ (r * ⌊r⌋),√ (r * (⌊r⌋-1)),√ (r * (⌊r⌋-2))} := by
        intro x ;simp
        intro hx1 hx2 hx3
        have h2 : ⌊x⌋ ≤ ⌊r⌋ := by exact Int.le_floor.mpr hx3
        have h3 : ⌊r⌋-3 < ⌊x⌋ := by
          have : ⌊r-3⌋ < ⌊x⌋ := by exact Int.floor_lt.mpr hx2
          simp at this ;exact this
        rcases Int.le_iff_lt_or_eq.mp h2 with (h|h)
        rcases Int.le_iff_eq_or_lt.mp (Int.le_sub_one_of_lt h) with (h'|h')
        · rw [h'] at hx1 ;right ;left ;rw [hx1] ;simp
        rcases Int.le_iff_eq_or_lt.mp (Int.le_sub_one_of_lt h') with (h'|h')
        · rw [h'] at hx1 ;right ;right ;rw [hx1] ;simp ;ring_nf
        linarith
        rw [h] at hx1 ;left ;rw [hx1]
      exact fun ⦃a⦄ a_1 ↦ this' (this a_1)
    have h1' : {x | 0 < x ∧ x ^ 2 = r * ↑⌊x⌋}.ncard ≤ 3 := by
      have this'' : ({√ (r * ⌊r⌋),√ (r * (⌊r⌋-1)),√ (r * (⌊r⌋-2))} : Set ℝ).ncard = 3 := by
        refine Set.ncard_eq_three.mpr ?_
        use √ (r * ⌊r⌋),√ (r * (⌊r⌋-1)),√ (r * (⌊r⌋-2)) ;simp
        have eq1 : √(r * ↑⌊r⌋) ^ 2 = r * ↑⌊r⌋ := by
          refine Real.sq_sqrt ?_ ;apply mul_nonneg ;linarith ;simp
          refine Int.floor_nonneg.mpr ?_ ;linarith
        have eq2 : √(r * (↑⌊r⌋-1)) ^ 2 = r * (↑⌊r⌋-1) := by
          refine Real.sq_sqrt ?_ ;apply mul_nonneg ;linarith ;simp
          refine Int.cast_one_le_of_pos ?_ ;refine Int.floor_pos.mpr ?_ ;linarith
        have eq3 : √(r * (↑⌊r⌋-2)) ^ 2 = r * (↑⌊r⌋-2) := by
          refine Real.sq_sqrt ?_ ;apply mul_nonneg ;linarith ;simp
          rw [← Int.cast_two] ;apply Int.cast_le.mpr ;refine Int.le_floor.mpr ?_ ;simp ;linarith
        constructor
        · by_contra!
          have : √(r * ↑⌊r⌋) ^ 2 = √(r * (↑⌊r⌋ - 1)) ^ 2 := by rw [this]
          rw [eq1,eq2] at this ;simp at this
          rcases this with this|this ;linarith ;linarith
        constructor
        · by_contra!
          have : √(r * ↑⌊r⌋) ^ 2 = √(r * (↑⌊r⌋ - 2)) ^ 2 := by rw [this]
          rw [eq1,eq3] at this ;simp at this
          rcases this with this|this ;linarith ;linarith
        · by_contra!
          have : √(r * (↑⌊r⌋ - 1)) ^ 2 = √(r * (↑⌊r⌋ - 2)) ^ 2 := by rw [this]
          rw [eq2,eq3] at this ;simp at this
          rcases this with this|this ;linarith
      rw [← this''] ;apply Set.ncard_le_ncard ;exact hsub ;simp
    -- Now suppose that $k$ is a positive integer in the interval $[r-2, r]$.
    -- There are at least two such positive integers.
    -- Observe that $k \leq \sqrt{r k} \leq \sqrt{(k+2) k} &lt; k+1$ and so $r k = r\lfloor\sqrt{r k}\rfloor$.
    -- We conclude that the equation $x^{2}=r\lfloor x\rfloor$ has at least two positive solutions, namely $x=\sqrt{r k}$ with $k \in [r-2, r]$.
    have h2 : {√ (r * ⌊r⌋),√ (r * (⌊r⌋-1))} ⊆ {x | 0 < x ∧ x ^ 2 = r * ↑⌊x⌋} := by
      intro x ;simp ;intro hx
      rcases hx with (hx|hx)
      · simp [hx] ;constructor
        · refine mul_pos (by linarith) ?_ ;simp ;refine Int.floor_pos.mpr ?_ ;linarith
        rw [Real.sq_sqrt (?_)]
        simp ;left
        · apply Int.floor_eq_iff.mpr ;constructor
          · have : √(r * ↑⌊r⌋) ≤ r := by
              refine Real.sqrt_le_iff.mpr ?_
              constructor ;linarith ;rw [pow_two] ;refine mul_le_mul_of_nonneg (by simp) ?_ (by linarith) (by linarith)
              exact Int.floor_le r
            exact le_trans (by apply Int.floor_le) this
          refine Int.floor_le_iff.mp (Int.le_floor.mpr ((Real.le_sqrt' ?_).mpr ?_))
          simp ;refine Int.floor_pos.mpr ?_ ;linarith
          rw [pow_two] ;apply mul_le_mul (Int.floor_le r) (by simp) (by simp ;refine Int.floor_nonneg.mpr ?_ ;linarith) (by linarith)
        have : 0 < r * ↑⌊r⌋ := by refine mul_pos (by linarith) ?_ ;simp ;refine Int.floor_pos.mpr ?_ ;linarith
        linarith
      have h2 : (2 :ℝ) ≤ ↑⌊r⌋ := by rw [← Int.cast_two] ;apply Int.cast_le.mpr ;refine Int.le_floor.mpr ?_ ;simp ;linarith
      · simp [hx] ;constructor
        · refine mul_pos (by linarith) ?_ ;simp ;rw [← Int.cast_one] ;apply Int.cast_lt.mpr ;refine Int.le_floor.mpr ?_ ;simp ;linarith
        rw [Real.sq_sqrt (?_)]
        simp ;left
        have hl : ↑⌊r⌋ - 1 ≤  √(r * (↑⌊r⌋ - 1)) := by
          refine (Real.le_sqrt' ?_).mpr ?_
          simp ;linarith
          rw [pow_two] ;apply mul_le_mul ?_ (by simp) (by simp ;linarith) (by linarith)
          simp
          have : ↑⌊r⌋ ≤ r:= Int.floor_le r
          linarith
        have hr : √(r * (↑⌊r⌋ - 1)) < ↑⌊r⌋ := by
          refine (Real.sqrt_lt' (by simp ;refine Int.floor_pos.mpr (by linarith))).mpr ?_
          have : r * (↑⌊r⌋ - 1) < (↑⌊r⌋ + 1) * (↑⌊r⌋ - 1) := by
            apply (mul_lt_mul_right (by simp;linarith)).mpr ;exact Int.lt_floor_add_one r
          linarith
        apply Int.floor_le_floor at hl ;simp at hl
        apply Int.floor_lt.mpr at hr
        have : ⌊r⌋ = ⌊√(r * (↑⌊r⌋ - 1))⌋ + 1 := by
          exact Eq.symm (Int.le_antisymm hr hl)
        nth_rewrite 1 [this] ;simp
        have : 0 < r * (↑⌊r⌋-1) := by refine mul_pos (by linarith) ?_ ;simp ;rw [← Int.cast_one] ;apply Int.cast_lt.mpr ;refine Int.le_floor.mpr ?_ ;simp ;linarith
        linarith
    have h2' : 2 ≤ {x | 0 < x ∧ x ^ 2 = r * ↑⌊x⌋}.ncard := by
      have : ({√ (r * ⌊r⌋),√ (r * (⌊r⌋-1))} : Set ℝ).ncard = 2 := by
        refine Set.ncard_eq_two.mpr ?_
        use √ (r * ⌊r⌋),√ (r * (⌊r⌋-1)) ;simp
        by_contra!
        have : √(r * ↑⌊r⌋) ^ 2 = √(r * (↑⌊r⌋ - 1)) ^ 2 := by rw [this]
        have eq1 : √(r * ↑⌊r⌋) ^ 2 = r * ↑⌊r⌋ := by
          refine Real.sq_sqrt ?_ ;apply mul_nonneg ;linarith ;simp
          refine Int.floor_nonneg.mpr ?_ ;linarith
        have eq2 : √(r * (↑⌊r⌋-1)) ^ 2 = r * (↑⌊r⌋-1) := by
          refine Real.sq_sqrt ?_ ;apply mul_nonneg ;linarith ;simp
          refine Int.cast_one_le_of_pos ?_ ;refine Int.floor_pos.mpr ?_ ;linarith
        rw [eq1,eq2] at this ;simp at this
        rcases this with this|this ;linarith ;linarith
      nth_rewrite 1 [← this] ;refine Set.ncard_le_ncard h2 ?_
      apply Set.Finite.subset ?_ hsub ;simp
    refine Nat.le_and_le_add_one_iff.mp ?_
    constructor ;exact h2' ;ring_nf ;exact h1'