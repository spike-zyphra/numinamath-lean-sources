import Mathlib
open Real Set

/--

Problem statement (Main theorem of this file):
If the graph of the odd function $y=f(x)$ defined on $\mathbf{R}$ is symmetric about the line $x=1$, and when $0<{}x\leqslant 1$, $f(x)={{\log }_
{3}}x$, then the sum of all real roots of the equation $f(x)=-\frac{1}{3}+f(0)$ in the interval $(0,10)$ is
-/


theorem algebra_624265 {f : ℝ → ℝ} (hfodd : ∀ x, f (-x) = -f x)
(hsymm : ∀ x, f (1 + x) = f (1 - x))
(hf : ∀ x ∈ Ioc 0 1, f x = logb 3 x)
(S : Finset ℝ)
(hS : ↑S = {x | x ∈ Ioo 0 10 ∧ f x = -1 / 3 + f 0})
: ∑ x ∈ S, x = 30 := by

  have h_f_at0 : f 0 = 0 := by
    specialize hfodd 0
    simp at hfodd
    linarith

  -- Simplify equation by substituting f(0) = 0
  replace hS : ↑S = {x | x ∈ Ioo 0 10 ∧ f x = -1 / 3} := by
    rw [h_f_at0, add_zero] at hS
    exact hS

  have h_f_at2 : f 2 = 0 := by
    have := hsymm 1
    simp at this
    ring_nf at this
    rw [h_f_at0] at this
    exact this

  -- Prove that f has period 4
  have f_period4 : ∀ x, f (x + 4) = f x := by
    intro x
    have h1 :  f (x + 4) = f (-2 - x) := by
      have := hsymm (x + 3)
      ring_nf at this
      rw [←this]
      ring_nf

    have h2 : f (-2 - x) = - f (2 + x):= by
      have := hfodd (2 + x)
      rw [←this]
      ring_nf

    have h3 : f (2 + x) = f (-x) := by
      have := hsymm (x + 1)
      ring_nf at this
      exact this

    rw [h1, h2, h3, hfodd]
    simp

  have h_f_at4 : f 4 = 0 := by
    have := f_period4 0
    simp at this
    rw [h_f_at0] at this
    exact this

  -- Define f in different intervals
  -- For 0 < x ≤ 1, we know f(x) = logb 3 x from hypothesis
  have h_0_1 : ∀ x ∈ Ioc 0 1, f x = logb 3 x := hf

  have hf' : ∀ x ∈ Ioo 0 1, f x = logb 3 x := by
    intros x hx
    exact hf x ⟨hx.1, le_of_lt hx.2⟩

  -- For 1 < x ≤ 2, use symmetry about x=1
  have h_1_2 : ∀ x ∈ Ioc 1 2,  f x = if x = 2 then 0 else logb 3 (2 - x) := by
    intro x hx
    split_ifs with h_at_2
    . rw [h_at_2]
      exact h_f_at2
    . have h_mirror : 2 - x ∈ Ioo 0 1 := by
        simp
        simp at hx
        have h1: x < 2 := lt_of_le_of_ne (by tauto) h_at_2
        have h2: 2 - x < 1 := by linarith
        exact ⟨h1, h2⟩

      rw [←hf' (2 - x) h_mirror]
      have := hsymm (x - 1)
      simp at this
      ring_nf at this
      exact this

  have h_2_3 : ∀ x ∈ Ioc 2 3, f x = -logb 3 (x - 2) := by
    intro x hx
    have h_mirror : x - 2 ∈ Ioc 0 1 := by
      simp
      ring_nf
      exact hx

    rw [← hf (x - 2) h_mirror]
    have := hsymm (x - 1)
    ring_nf at this
    rw [this]
    have := hfodd (x-2)
    ring_nf at this
    rw [this]
    ring_nf

  have h_3_4 : ∀ x ∈ Ioc 3 4, f x = if x = 4 then 0 else -logb 3 (4 - x) := by
    intro x hx
    split_ifs with h_at_4
    . rw [h_at_4]
      exact h_f_at4
    . have h_mirror : 4 - x ∈ Ioo 0 1 := by
        simp
        simp at hx
        have h1: x < 4 := lt_of_le_of_ne (by tauto) h_at_4
        have h2: 4 - x < 1 := by linarith
        exact ⟨h1, h2⟩

      rw [←hf' (4 - x) h_mirror]
      have := f_period4 (- x)
      ring_nf at this
      rw [this]
      have := hfodd (-x)
      ring_nf at this
      exact this

  -- Find roots of f(x) = -1/3 in each interval
  -- Define the set of roots in each interval
  let S_0_1 := {x | x ∈ Ioc 0 1 ∧ f x = -1/3}
  let S_1_2 := {x | x ∈ Ioc 1 2 ∧ f x = -1/3}
  let S_2_3 := {x | x ∈ Ioc 2 3 ∧ f x = -1/3}
  let S_3_4 := {x | x ∈ Ioc 3 4 ∧ f x = -1/3}
  let S_4_5 := {x | x ∈ Ioc 4 5 ∧ f x = -1/3}
  let S_5_6 := {x | x ∈ Ioc 5 6 ∧ f x = -1/3}
  let S_6_7 := {x | x ∈ Ioc 6 7 ∧ f x = -1/3}
  let S_7_8 := {x | x ∈ Ioc 7 8 ∧ f x = -1/3}
  let S_8_9 := {x | x ∈ Ioc 8 9 ∧ f x = -1/3}
  let S_9_10 := {x | x ∈ Ioo 9 10 ∧ f x = -1/3}

  -- Calculate the exact value of each root
  -- Value of 3^(-1/3)
  let root := (3 : ℝ) ^ (-(1/3) : ℝ)

  have h_root_pos : 0 < root := by positivity
  have h_root_lt_1 : root < 1 := by apply rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have h_root : logb 3 root = -1 / 3 := by
    rw [logb_rpow (by norm_num) (by norm_num)]
    linarith

  have S_0_1_value : S_0_1 = {root} := by
    ext x; unfold S_0_1; simp
    constructor
    . intro hx
      have := hx.2
      rw [h_0_1 x hx.1, ← h_root] at this
      apply logb_injOn_pos (by norm_num) at this
      . linarith
      . simp; exact hx.1.1
      . tauto
    . intro hx; rw [hx]
      have h_range : (0 < root ∧ root ≤ 1) := by constructor; all_goals linarith
      constructor
      . exact h_range
      . rw [h_0_1 root h_range]
        exact h_root

  have S_1_2_value : S_1_2 = {2 - root} := by
    ext x; unfold S_1_2; simp
    constructor
    . intro hx
      by_cases h_at_2 : x = 2
      . have := hx.2
        rw [h_at_2] at this
        linarith
      . have : x < 2 := lt_of_le_of_ne (by tauto) h_at_2
        have h_eq := hx.2
        have h_f_eq := h_1_2 x hx.1
        split_ifs at h_f_eq
        rw [h_f_eq, ←h_root] at h_eq
        apply logb_injOn_pos (by norm_num) at h_eq
        . linarith
        . simp; assumption
        . tauto
    . intro hx; rw [hx]
      have h_range : (1 < 2 - root ∧ 2 - root ≤ 2) := by constructor; all_goals linarith
      constructor
      . exact h_range
      . rw [h_1_2 (2 - root) h_range]
        simp
        split_ifs
        . linarith
        . exact h_root

  -- Use periodicity to find roots in intervals (4,6) and (8,10)
  have S_4_5_value : S_4_5 = {4 + root} := by
    ext x; unfold S_4_5; simp
    constructor
    . intro hx
      have : x - 4 ∈ S_0_1 := by
        unfold S_0_1
        simp
        rw [← f_period4 (x - 4)]
        ring_nf
        exact hx
      rw [S_0_1_value] at this
      simp at this
      linarith
    . intro hx
      have : x - 4 ∈ S_0_1 := by rw [S_0_1_value, hx]; simp
      unfold S_0_1 at this
      simp at this
      ring_nf at this
      rw [← f_period4 (-4 + x)] at this
      ring_nf at this
      exact this

  have S_5_6_value : S_5_6 = {6 - root} := by
    ext x; unfold S_5_6; simp
    constructor
    . intro hx
      have : x - 4 ∈ S_1_2 := by
        unfold S_1_2
        simp
        rw [← f_period4 (x - 4)]
        ring_nf
        simp
        ring_nf
        exact hx
      rw [S_1_2_value] at this
      simp at this
      linarith
    . intro hx
      have : x - 4 ∈ S_1_2 := by
        rw [S_1_2_value, hx]
        simp
        ring_nf
      unfold S_1_2 at this
      simp at this
      ring_nf at this
      rw [← f_period4 (-4 + x)] at this
      ring_nf at this
      simp at this
      ring_nf at this
      exact this
  have S_8_9_value : S_8_9 = {8 + root} := by
    ext x; unfold S_8_9; simp
    constructor
    . intro hx
      have : x - 4 ∈ S_4_5 := by
        unfold S_4_5
        simp
        rw [← f_period4 (x - 4)]
        ring_nf
        simp
        ring_nf
        exact hx
      rw [S_4_5_value] at this
      simp at this
      linarith
    . intro hx
      have : x - 4 ∈ S_4_5 := by
        rw [S_4_5_value, hx]
        simp
        ring_nf
      unfold S_4_5 at this
      simp at this
      ring_nf at this
      rw [← f_period4 (-4 + x)] at this
      ring_nf at this
      simp at this
      ring_nf at this
      exact this

  have S_9_10_value : S_9_10 = {10 - root} := by
    ext x; unfold S_9_10; simp
    constructor
    . intro hx
      have : x - 4 ∈ S_5_6 := by
        unfold S_5_6
        simp
        rw [← f_period4 (x - 4)]
        ring_nf
        simp
        ring_nf
        exact ⟨ ⟨hx.1.1, le_of_lt hx.1.2⟩, hx.2⟩
      rw [S_5_6_value] at this
      simp at this
      linarith
    . intro hx
      have : x - 4 ∈ S_5_6 := by
        rw [S_5_6_value, hx]
        simp
        ring_nf
      unfold S_5_6 at this
      simp at this
      ring_nf at this
      rw [← f_period4 (-4 + x)] at this
      ring_nf at this
      simp at this
      ring_nf at this
      by_cases h_at_10 : x = 10
      . rw [h_at_10] at hx
        linarith
      . exact ⟨⟨(by linarith), (by linarith)⟩, this.2⟩
  -- Prove remaining intervals have no solutions
  have S_2_3_empty : S_2_3 = ∅ := by
    ext x
    simp
    intro hx
    unfold S_2_3 at hx
    simp at hx
    have h_eq : -1 / 3 = - logb 3 (x - 2) := by
      have := h_2_3 x hx.1
      rw [hx.2] at this
      exact this
    have : logb 3 (x - 2) ≤ 0 := by apply logb_nonpos (by norm_num) (by linarith) (by linarith)
    linarith

  have S_3_4_empty : S_3_4 = ∅ := by
    ext x
    simp
    intro hx
    unfold S_3_4 at hx
    simp at hx

    by_cases h_at_4 : x = 4
    . have h_eq := hx.2
      rw [h_at_4, h_f_at4] at h_eq
      linarith
    . have h_eq : -1 / 3 = - logb 3 (4 - x) := by
        have := h_3_4 x hx.1
        split_ifs at this
        rw [hx.2] at this
        exact this
      have : logb 3 (4 - x) ≤ 0 := by apply logb_nonpos (by norm_num) (by linarith) (by linarith)
      linarith

  have S_6_7_empty : S_6_7 = ∅ := by
    ext x
    simp
    intro hx
    unfold S_6_7 at hx
    simp at hx
    have : x - 4 ∈ S_2_3 := by
      have := f_period4 (x - 4)
      simp at this
      unfold S_2_3
      simp
      rw [← this]
      ring_nf
      simp
      ring_nf
      exact hx
    rw [S_2_3_empty] at this
    tauto
  have S_7_8_empty : S_7_8 = ∅ := by
    ext x
    simp
    intro hx
    unfold S_7_8 at hx
    simp at hx
    have : x - 4 ∈ S_3_4 := by
      have := f_period4 (x - 4)
      simp at this
      unfold S_3_4
      simp
      rw [← this]
      ring_nf
      simp
      ring_nf
      exact hx
    rw [S_3_4_empty] at this
    tauto

  -- Combine all results to get the final sum = 30
  have h_S_result : S = {10 - root, 8 + root, 6 - root, 4 + root, 2 - root, root} := by
    have : {x | x ∈ Ioo 0 10 ∧ f x = -1 / 3} = {10 - root, 8 + root, 6 - root, 4 + root, 2 - root, root} := by
      ext x
      simp
      constructor
      . intro ⟨ hx, hf ⟩
        by_cases h01 : x ∈ Ioc 0 1
        . have : x ∈ S_0_1 := ⟨ h01, hf ⟩
          rw [S_0_1_value] at this; tauto
        . by_cases h12 : x ∈ Ioc 1 2
          . have : x ∈ S_1_2 := ⟨ h12, hf ⟩
            rw [S_1_2_value] at this; tauto
          . by_cases h23 : x ∈ Ioc 2 3
            . have : x ∈ S_2_3 := ⟨ h23, hf ⟩
              rw [S_2_3_empty] at this; tauto
            . by_cases h34 : x ∈ Ioc 3 4
              . have : x ∈ S_3_4 := ⟨ h34, hf ⟩
                rw [S_3_4_empty] at this; tauto
              . by_cases h45 : x ∈ Ioc 4 5
                . have : x ∈ S_4_5 := ⟨ h45, hf ⟩
                  rw [S_4_5_value] at this; tauto
                . by_cases h56 : x ∈ Ioc 5 6
                  . have : x ∈ S_5_6 := ⟨ h56, hf ⟩
                    rw [S_5_6_value] at this; tauto
                  . by_cases h67 : x ∈ Ioc 6 7
                    . have : x ∈ S_6_7 := ⟨ h67, hf ⟩
                      rw [S_6_7_empty] at this; tauto
                    . by_cases h78 : x ∈ Ioc 7 8
                      . have : x ∈ S_7_8 := ⟨ h78, hf ⟩
                        rw [S_7_8_empty] at this; tauto
                      . by_cases h89 : x ∈ Ioc 8 9
                        . have : x ∈ S_8_9 := ⟨ h89, hf ⟩
                          rw [S_8_9_value] at this; tauto
                        . by_cases h910 : x ∈ Ioo 9 10
                          . have : x ∈ S_9_10 := ⟨ h910, hf ⟩
                            rw [S_9_10_value] at this; tauto
                          . simp at *
                            have := h910 (h89 (h78 (h67 (h56 (h45 (h34 (h23 (h12 (h01 hx.1)))))))))
                            linarith
      . intro h
        cases' h with h1 ha
        . have : x ∈ S_9_10 := by rw [S_9_10_value]; simp; exact h1
          exact ⟨⟨(by linarith [this.1.1]), (by linarith [this.1.2])⟩, this.2⟩
        . cases' ha with h2 hb
          . have : x ∈ S_8_9 := by rw [S_8_9_value]; simp; exact h2
            exact ⟨⟨(by linarith [this.1.1]), (by linarith [this.1.2])⟩, this.2⟩
          . cases' hb with h3 hc
            . have : x ∈ S_5_6 := by rw [S_5_6_value]; simp; exact h3
              exact ⟨⟨(by linarith [this.1.1]), (by linarith [this.1.2])⟩, this.2⟩
            . cases' hc with h4 h5
              . have : x ∈ S_4_5 := by rw [S_4_5_value]; simp; exact h4
                exact ⟨⟨(by linarith [this.1.1]), (by linarith [this.1.2])⟩, this.2⟩
              . cases' h5 with h6 h7
                . have : x ∈ S_1_2 := by rw [S_1_2_value]; simp; exact h6
                  exact ⟨⟨(by linarith [this.1.1]), (by linarith [this.1.2])⟩, this.2⟩
                . have : x ∈ S_0_1 := by rw [S_0_1_value]; simp; exact h7
                  exact ⟨⟨this.1.1, (by linarith [this.1.2])⟩, this.2⟩

    apply Finset.coe_injective
    rw [hS, this]
    simp

  have h_final_sum : ∑ x ∈ S, x = 30 := by
    rw [h_S_result]
    repeat rw [Finset.sum_insert]
    rw [Finset.sum_singleton]
    ring_nf
    . simp; linarith
    . simp;linarith
    . simp
      have : ¬6 - root = 4 + root := by linarith
      have : ¬6 - root = root := by linarith
      tauto
    . simp
      have : ¬8 + root = 6 - root := by linarith
      have : ¬8 + root = 2 - root := by linarith
      tauto
    . simp
      have : ¬10 - root = 8 + root := by linarith
      have : ¬10 - root = 4 + root := by linarith
      have : ¬10 - root = root := by linarith
      tauto

  exact h_final_sum
