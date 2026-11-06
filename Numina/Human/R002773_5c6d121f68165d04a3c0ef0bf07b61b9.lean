import Mathlib

set_option maxHeartbeats 600000

/- If the equation $\frac{|x|}{x+6}=k x^{2}$ has four distinct real solutions for $x$,
then the range of real values for $k$ is $\qquad$.-/

theorem algebra_111245 (k : ℝ):
     (∃ x1 x2 x3 x4 : ℝ, x1 < x2 ∧ x2 < x3 ∧ x3 < x4 ∧
      abs x1 / (x1 + 6) = k * x1^2 ∧ abs x2 / (x2 + 6) = k * x2^2 ∧
      abs x3 / (x3 + 6) = k * x3^2 ∧ abs x4 / (x4 + 6) = k * x4^2) ↔
    k ∈ Set.Ioi (1 / 9) := by

    constructor

    -- the forward direction, show that k must be more than 1 / 9
    .
      intro h
      obtain ⟨x1, x2, x3, x4, l1, l2, l3, h1, h2, h3, h4⟩ := h

      -- we first show that k ≠ 0
      have hk: k ≠ 0 := by
        by_contra! o
        simp [o] at *
        rcases h1 with h1 | h1
        <;> rcases h2 with h2 | h2
        <;> rcases h3 with h3 | h3
        <;> linarith

      -- we first show that 0 ≤ x3
      have r3: 0 ≤ x3 := by
        by_contra! r3
        clear l3 h4
        rw [show |x3| = -x3 by apply abs_of_nonpos; linarith] at h3
        rw [show |x2| = -x2 by apply abs_of_nonpos; linarith] at h2
        rw [show |x1| = -x1 by apply abs_of_nonpos; linarith] at h1
        have u1: x1 + 6 ≠ 0 := by
          by_contra! o
          replace o: x1 = -6 := by linarith
          simp [o] at h1
          tauto
        have u2: x2 + 6 ≠ 0 := by
          by_contra! o
          replace o: x2 = -6 := by linarith
          simp [o] at h2
          tauto
        have u3: x3 + 6 ≠ 0 := by
          by_contra! o
          replace o: x3 = -6 := by linarith
          simp [o] at h3
          tauto
        field_simp at h1 h2 h3
        clear u1 u2 u3
        have v1: x1 ≠ 0 := by linarith
        have v2: x2 ≠ 0 := by linarith
        have v3: x3 ≠ 0 := by linarith
        replace h1: x1 * (k * x1 ^ 2 + 6 * k * x1 + 1) = 0 := by nlinarith
        replace h2: x2 * (k * x2 ^ 2 + 6 * k * x2 + 1) = 0 := by nlinarith
        replace h3: x3 * (k * x3 ^ 2 + 6 * k * x3 + 1) = 0 := by nlinarith
        simp [v1, v2, v3] at h1 h2 h3
        -- then we apply vieta's lemma
        have v1: k * (x1 - x2) * ((x1 + x2) + 6) = 0 := by
          nlinarith
        have v2: k * (x3 - x2) * ((x3 + x2) + 6) = 0 := by
          nlinarith
        simp [hk] at v1 v2
        have o1: x1 - x2 ≠ 0 := by linarith
        have o2: x3 - x2 ≠ 0 := by linarith
        simp [o1, o2] at v1 v2
        linarith

      -- similarly, we show that x2 ≤ 0
      have r2: x2 ≤ 0 := by
        by_contra! r2
        clear l1 h1
        rw [show |x3| = x3 by apply abs_of_nonneg; linarith] at h3
        rw [show |x2| = x2 by apply abs_of_nonneg; linarith] at h2
        rw [show |x4| = x4 by apply abs_of_nonneg; linarith] at h4
        have u4: x4 + 6 ≠ 0 := by
          by_contra! o
          replace o: x4 = -6 := by linarith
          simp [o] at h4
          tauto
        have u2: x2 + 6 ≠ 0 := by
          by_contra! o
          replace o: x2 = -6 := by linarith
          simp [o] at h2
          tauto
        have u3: x3 + 6 ≠ 0 := by
          by_contra! o
          replace o: x3 = -6 := by linarith
          simp [o] at h3
          tauto
        field_simp at h4 h2 h3
        clear u4 u2 u3
        have v4: x4 ≠ 0 := by linarith
        have v2: x2 ≠ 0 := by linarith
        have v3: x3 ≠ 0 := by linarith
        replace h4: x4 * (k * x4 ^ 2 + 6 * k * x4 - 1) = 0 := by nlinarith
        replace h2: x2 * (k * x2 ^ 2 + 6 * k * x2 - 1) = 0 := by nlinarith
        replace h3: x3 * (k * x3 ^ 2 + 6 * k * x3 - 1) = 0 := by nlinarith
        simp [v4, v2, v3] at h4 h2 h3
        -- then we apply vieta's lemma
        have v1: k * (x3 - x2) * ((x3 + x2) + 6) = 0 := by
          nlinarith
        have v2: k * (x3 - x4) * ((x3 + x4) + 6) = 0 := by
          nlinarith
        simp [hk] at v1 v2
        have o1: x3 - x2 ≠ 0 := by linarith
        have o2: x3 - x4 ≠ 0 := by linarith
        simp [o1, o2] at v1 v2
        linarith

      -- then we can take out the abs sign
      rw [show |x3| = x3 by apply abs_of_nonneg; linarith] at h3
      rw [show |x2| = -x2 by apply abs_of_nonpos; linarith] at h2
      rw [show |x4| = x4 by apply abs_of_nonneg; linarith] at h4
      rw [show |x1| = -x1 by apply abs_of_nonpos; linarith] at h1

      -- then we can show that x3 = 0
      have f3: x3 = 0 := by
        by_contra! o
        have o':= o
        replace o: 0 < x3 := by
          by_contra! g
          replace g: x3 = 0 := by linarith
          tauto
        clear h1 h2 l1 l2 r2 r3
        have o1: x3 + 6 ≠ 0 := by linarith
        have o2: x4 + 6 ≠ 0 := by linarith
        field_simp at h3 h4
        replace h3: x3 * (k * x3 * (x3 + 6) - 1) = 0 := by nlinarith
        simp [o'] at h3
        replace h4: x4 * (k * x4 * (x4 + 6) - 1) = 0 := by nlinarith
        simp at h4
        have o'': x4 ≠ 0 := by linarith
        simp [o''] at h4
        clear o' o''
        have j: k * (x3 - x4) * (x3 + x4 + 6) = 0 := by nlinarith
        simp [hk] at j
        rcases j with j | j
        .
          linarith
        .
          linarith

      simp [f3] at *

      -- we show that 0 < k
      have o1: 0 < k := by
        by_contra! l
        have r: 0 < x4 := by linarith
        clear *- r h4 l hk
        have u: x4 + 6 ≠ 0 := by linarith
        field_simp at h4
        replace h4: x4 * (k * x4 * (x4 + 6) - 1) = 0 := by nlinarith
        simp at h4
        rcases h4 with v | v
        .
          linarith
        .
          have r1: k * x4 ≤ 0 := by nlinarith
          have r2: k * x4 * (x4 + 6) ≤ 0 := by nlinarith
          replace v: k * x4 * (x4 + 6) = 1 := by linarith
          rw [v] at r2
          norm_num at r2

      -- at last, we prove by contradiction
      simp
      by_contra! o

      -- then we can find contradiction from x1 and x2
      clear l3 h4 h3 r2
      have u1: x1 + 6 ≠ 0 := by
        by_contra! c
        simp [c, hk] at h1
        linarith
      have u2: x2 + 6 ≠ 0 := by
        by_contra! c
        simp [c, hk] at h2
        linarith
      field_simp at h1 h2
      clear u1 u2
      replace h1: x1 * (k * x1 * (x1 + 6) + 1) = 0 := by nlinarith
      replace h2: x2 * (k * x2 * (x2 + 6) + 1) = 0 := by nlinarith
      have v1: x1 ≠ 0 := by linarith
      have v2: x2 ≠ 0 := by linarith
      simp [v1, v2] at h1 h2
      clear v1 v2
      replace h1: 9 - 1 / k = (x1 + 3) ^ 2 := by
        field_simp
        nlinarith
      have v: 9⁻¹ ≤ k := by
        suffices 0 ≤ 9 - 1 / k by
          clear *- this o1
          field_simp
          have o2:= o1
          replace o1: 0 < 1 / k := by
            field_simp
            tauto
          apply le_of_one_div_le_one_div
          tauto
          linarith
        rw [h1]
        apply sq_nonneg
      have f: k = 9⁻¹ := by linarith
      simp [f] at *
      symm at h1
      simp at h1
      replace h2: (x2 + 3) ^ 2 = 0 := by nlinarith
      simp at h2
      linarith


    -- the backward direction, show that such k satisfy the condition
    .
      intro h
      simp at h
      have o: k ≠ 0 := by linarith
      set x1:= -3 - √(9 * k ^ 2 - k) / k
      set x2:= -3 + √(9 * k ^ 2 - k) / k
      set x3:= (0: ℝ)
      set x4:= -3 + √(9 * k ^ 2 + k) / k
      use x1, x2, x3, x4
      have l1: x2 < 0 := by
        simp [x2]
        rw [div_lt_iff₀']
        rw [Real.sqrt_lt']
        nlinarith
        linarith
        linarith
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      .
        simp [x1, x2]
        have o: 0 < √(9 * k ^ 2 - k) := by
          rw [Real.sqrt_pos]
          nlinarith
        field_simp
        apply div_lt_div_of_pos_right
        linarith
        linarith
      .
        simp [x3]
        tauto
      .
        simp [x3, x4]
        rw [lt_div_iff₀]
        apply Real.lt_sqrt_of_sq_lt
        nlinarith
        linarith
      .
        have u: x1 < 0 := by
          simp [x1]
          have o1: 0 < √(9 * k ^ 2 - k) := by
            rw [Real.sqrt_pos]
            nlinarith
          rw [lt_div_iff₀]
          linarith
          linarith
        rw [show |x1| = -x1 by apply abs_of_nonpos; linarith]
        have i: k * x1 ^ 2 * (x1 + 6) + x1 = 0 := by
          rw [show k * x1 ^ 2 * (x1 + 6) + x1 = x1 * (k * x1 * (x1 + 6) + 1) by ring]
          suffices k * x1 * (x1 + 6) + 1 = 0 by simp [this]
          simp [x1]
          ring_nf
          have v: √(-k + k ^ 2 * 9) ^ 2 = -k + k ^ 2 * 9 := by
            symm
            rw [← Real.sqrt_eq_iff_eq_sq]
            nlinarith
            apply Real.sqrt_nonneg
          simp [v]
          field_simp
          ring
        have v: x1 + 6 ≠ 0 := by
          by_contra! v
          simp [v] at i
          linarith
        field_simp
        linarith
      .
        have u: x2 < 0 := by
          simp [x2]
          have o1: 0 < √(9 * k ^ 2 - k) := by
            rw [Real.sqrt_pos]
            nlinarith
          rw [div_lt_iff₀']
          rw [Real.sqrt_lt']
          nlinarith
          linarith
          linarith
        rw [show |x2| = -x2 by apply abs_of_nonpos; linarith]
        have i: k * x2 ^ 2 * (x2 + 6) + x2 = 0 := by
          rw [show k * x2 ^ 2 * (x2 + 6) + x2 = x2 * (k * x2 * (x2 + 6) + 1) by ring]
          suffices k * x2 * (x2 + 6) + 1 = 0 by simp [this]
          simp [x2]
          ring_nf
          have v: √(-k + k ^ 2 * 9) ^ 2 = -k + k ^ 2 * 9 := by
            symm
            rw [← Real.sqrt_eq_iff_eq_sq]
            nlinarith
            apply Real.sqrt_nonneg
          simp [v]
          field_simp
          ring
        have v: x2 + 6 ≠ 0 := by
          by_contra! v
          simp [v] at i
          linarith
        field_simp
        linarith
      .
        simp [x3]
      .
        have j: 0 < x4 := by
          simp [x4]
          rw [lt_div_iff₀']
          apply Real.lt_sqrt_of_sq_lt
          nlinarith
          linarith
        rw [show |x4| = x4 by apply abs_of_nonneg; linarith]
        have n: x4 = k * x4 ^ 2 * (x4 + 6) := by
          suffices k * x4 ^ 2 * (x4 + 6) - x4 = 0 by linarith
          rw [show k * x4 ^ 2 * (x4 + 6) - x4 = x4 * (k * x4 * (x4 + 6) - 1) by ring]
          suffices k * x4 * (x4 + 6) - 1 = 0 by simp [this]
          simp [x4]
          ring_nf
          have p: √(k + k ^ 2 * 9) ^ 2 = k + k ^ 2 * 9 := by
            symm
            rw [← Real.sqrt_eq_iff_eq_sq]
            nlinarith
            apply Real.sqrt_nonneg
          simp [p]
          field_simp
          ring
        have o: x4 + 6 ≠ 0 := by
          by_contra! o
          simp [o] at n
          linarith
        field_simp
        linarith