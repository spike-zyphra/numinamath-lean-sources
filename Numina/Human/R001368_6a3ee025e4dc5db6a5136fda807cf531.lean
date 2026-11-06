import Mathlib



/- 6. (CZS 4) Find the real values of $p$ for which the equation  $$ \sqrt{2 p+1-x^{2}}+\sqrt{3 x+p+4}=\sqrt{x^{2}+9 x+3 p+9} $$  in $x$ has exactly two real distinct roots $(\sqrt{t}$ means the positive square root of $t$ ). -/
theorem algebra_23754 {p : ℝ} :
  {x:ℝ | √(2*p+1-x^2) + √(3*x+p+4) = √(x^2+9*x+3*p+9) ∧
  0 ≤ 2*p+1-x^2 ∧ 0 ≤ 3*x+p+4 ∧ 0 ≤ x^2+9*x+3*p+9}.encard = 2 ↔
  ((-1/4 < p ∧ p ≤ 0) ∨ (p ≥ 2)) := by

  -- simplify the equation
  have hq {x q:ℝ} (heq: √(2*p+1-x^2) + √(3*x+p+4) = √(x^2+9*x+3*p+9))
    (q_def: q = x^2 + x - p) (h_nng1: 0 ≤ 2*p+1-x^2)
    (h_nng2: 0 ≤ 3*x+p+4) (h_nng3: 0 ≤ x^2+9*x+3*p+9):
    q * (2*q - 2*(x+2)^2 - (x+1)^2) = 0 := by
    -- express p in terms of q
    have h1: 2*p+1-x^2 = (x+1)^2 - 2*q := by
      rw [q_def]
      ring
    have h2: 3*x+p+4 = (x+2)^2 - q := by
      rw [q_def]
      ring
    have h3: x^2+9*x+3*p+9 = (2*x+3)^2 - 3*q := by
      rw [q_def]
      ring
    --take square
    rw [← sq_eq_sq₀ (by positivity) (by positivity)] at heq
    have h4: (√(2*p+1-x^2) + √(3*x+p+4))^2 =
      (√(2*p+1-x^2))^2 + (√(3*x+p+4))^2 +
      2 * √(2*p+1-x^2) * √(3*x+p+4) := by ring
    rw [Real.sq_sqrt h_nng1, Real.sq_sqrt h_nng2] at h4
    replace h4: (√(2*p+1-x^2) + √(3*x+p+4))^2 =
      (x+1)^2+(x+2)^2-3*q + 2 * √(((x+1)^2 - 2*q) * ((x+2)^2 - q)) := by
      rw [mul_assoc 2 _, ← Real.sqrt_mul h_nng1] at h4
      rw [h4, h1, h2]
      ring
    rw [h4, Real.sq_sqrt h_nng3, h3] at heq
    replace heq: 2 * √(((x+1)^2 - 2*q) * ((x+2)^2 - q)) =
      2 * ((x+1) * (x+2)) := by
      linarith only [heq]
    --take square again, done.
    simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at heq
    rw [h1] at h_nng1
    rw [h2] at h_nng2
    have: 0 ≤ (x+1)*(x+2) := by
      rw [← heq]
      simp
    rw [← sq_eq_sq₀ (by positivity) this,
    Real.sq_sqrt (mul_nonneg h_nng1 h_nng2)] at heq
    linarith only [heq]

  -- thus q must equal zero, otherwise number inside the square root is negative, contradiction.
  have q_zero {x q:ℝ} (heq: √(2*p+1-x^2) + √(3*x+p+4) = √(x^2+9*x+3*p+9))
    (q_def: q = x^2 + x - p) (h_nng1: 0 ≤ 2*p+1-x^2)
    (h_nng2: 0 ≤ 3*x+p+4) (h_nng3: 0 ≤ x^2+9*x+3*p+9):
    q = 0 := by
    specialize hq heq q_def h_nng1 h_nng2 h_nng3
    rw [mul_eq_zero] at hq
    rcases hq with hq | hq
    · exact hq
    · replace hq: 2*q = 2*(x+2)^2 + (x+1)^2 := by linarith only [hq]
      have hq': q = (x+2)^2 + (x+1)^2 / 2 := by
        linarith only [hq]
      have h1: 2*p+1-x^2 = (x+1)^2 - 2*q := by
        rw [q_def]
        ring
      rw [h1, hq] at h_nng1
      simp only [sub_add_cancel_right, Left.nonneg_neg_iff] at h_nng1
      have h2: 3*x+p+4 = (x+2)^2 - q := by
        rw [q_def]
        ring
      rw [h2, hq'] at h_nng2
      simp only [sub_add_cancel_left, Left.nonneg_neg_iff] at h_nng2
      have h3: (x+2)^2 = 0 := by
        apply le_antisymm ?_ (sq_nonneg _)
        exact nonpos_of_mul_nonpos_right h_nng1 (by norm_num)
      have h4: (x+1)^2 = 0 := by
        apply le_antisymm ?_ (sq_nonneg _)
        rw [div_nonpos_iff] at h_nng2
        have: ¬ (2: ℝ) ≤ 0 := by norm_num
        clear * - h_nng2 this
        tauto
      simp only [ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff] at h3 h4
      linarith only [h3, h4]

  -- substitute q = 0 back, the equation simplifies to |x+1| + |x+2| = |2x+3|
  have heq {x q: ℝ} (h: √(2*p+1-x^2) + √(3*x+p+4) = √(x^2+9*x+3*p+9))
    (q_def: q = x^2 + x - p) (h_nng1: 0 ≤ 2*p+1-x^2)
    (h_nng2: 0 ≤ 3*x+p+4) (h_nng3: 0 ≤ x^2+9*x+3*p+9):
    |x+1| + |x+2| = |2*x+3| := by
    have h1: 2*p+1-x^2 = (x+1)^2 - 2*q := by
      rw [q_def]
      ring
    have h2: 3*x+p+4 = (x+2)^2 - q := by
      rw [q_def]
      ring
    have h3: x^2+9*x+3*p+9 = (2*x+3)^2 - 3*q := by
      rw [q_def]
      ring
    specialize q_zero h q_def h_nng1 h_nng2 h_nng3
    simp only [h1, q_zero, mul_zero, sub_zero, h2, h3,
    Real.sqrt_sq_eq_abs] at h
    exact h

  -- for the absolute value equation holds, x cannot fall in (-2,-1)
  -- so if we claim q = x^2+x-p = 0, p = range of (x+1/2)^2 - 1/4 is determined.

  constructor

  · intro h
    rw [Set.encard_eq_two] at h
    rcases h with ⟨x, y, xney, hxy⟩
    -- for any z satisfy the condition, we have q = 0, and value of z is determined.
    -- also, by solving absolute value equation, we can decide range of z.
    have hz: ∀ z ∈ ({x, y}: Set ℝ), (z+1/2)^2 - 1/4 = p ∧
      (z ≤ -2 ∨ z ≥ -1) := by
      intro z hz
      rw [← hxy] at hz
      simp only [Set.mem_setOf_eq] at hz
      rcases hz with ⟨h, h_nng1, h_nng2, h_nng3⟩
      set q := z^2+z-p with q_def
      specialize heq h q_def h_nng1 h_nng2 h_nng3
      have hz: z ≤ -2 ∨ z ≥ -1 := by
        by_contra!
        have h1: z+1 < 0 := by linarith only [this]
        have h2: z+2 > 0 := by linarith only [this]
        rw [abs_of_neg h1, abs_of_pos h2] at heq
        replace heq: |2*z+3| = 1 := by
          rw [← heq]
          ring
        rw [abs_eq (by norm_num)] at heq
        rcases heq with heq | heq
        · have zeq: z = -1 := by linarith only [heq]
          simp [zeq] at this
        · have zeq: z = -2 := by linarith only [heq]
          simp [zeq] at this
      specialize q_zero h q_def h_nng1 h_nng2 h_nng3
      refine ⟨?_, hz⟩
      rw [q_def] at q_zero
      linarith only [q_zero]
    -- we claim it's impossible for p fall in (0,2) or = -1/4, otherwise only one solution.
    have hp1: p ≠ -1/4 := by
      rintro peq
      have h1: x ∈ ({x,y}: Set ℝ) := by simp
      have h2: y ∈ ({x,y}: Set ℝ) := by simp
      replace h1 := hz x h1
      replace h2 := hz y h2
      rw [peq] at h1 h2
      replace h1: (x+1/2)^2 = 0 := by
        linarith only [h1.left]
      replace h2: (y+1/2)^2 = 0 := by
        linarith only [h2.left]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff] at h1 h2
      absurd xney
      linarith only [h1, h2]
    have hp2 (ppos: 0 < p): p ≥ 2 := by
      by_contra! plt
      have h1: x ∈ ({x,y}: Set ℝ) := by simp
      have h2: y ∈ ({x,y}: Set ℝ) := by simp
      replace h1 := hz x h1
      replace h2 := hz y h2
      have {z:ℝ} (hhz: (z+1/2)^2-1/4 = p ∧ (z ≤ -2 ∨ z ≥ -1)):
        z = √(1/4 + p) - 1/2 := by
        have zeq': (z+1/2)^2 = (√(1/4 + p))^2:= by
          rw [Real.sq_sqrt]
          rw [← hhz.left]
          ring
          linarith only [ppos]
        rw [sq_eq_sq_iff_eq_or_eq_neg] at zeq'
        rcases zeq' with zeq | zeq
        · linarith only [zeq]
        · have hz1: z < -1 := by
            suffices -√(1/4 + p) < -1/2 by
              rw [← zeq] at this
              linarith only [this]
            suffices √(1/4 + p) > √((1/2)^2) by
              rw [Real.sqrt_sq (by norm_num)] at this
              linarith only [this]
            suffices 1/4+p > (1/2)^2 by
              apply (Real.sqrt_lt_sqrt_iff_of_pos ?_).mpr this
              linarith only [ppos]
            linarith only [ppos]
          have hz2: z ≤ -2 := by
            have := hhz.right
            rcases this with hz' | hz'
            · exact hz'
            · linarith only [hz1, hz']
          replace hz2: √(1/4+p) ≥ √((3/2)^2) := by
            rw [Real.sqrt_sq (by norm_num)]
            linarith only [zeq, hz2]
          rw [ge_iff_le, Real.sqrt_le_sqrt_iff] at hz2
          <;> linarith only [ppos, plt, hz2]
      replace h1 := this h1
      replace h2 := this h2
      absurd xney
      rw [h1, h2]
    by_cases hp: 0 < p
    · right; exact hp2 hp
    · suffices - 1/4 ≤ p by
        left
        push_neg at hp
        refine ⟨?_, hp⟩
        apply lt_of_le_of_ne this hp1.symm
      specialize hz x (by simp)
      rw [← hz.left]
      linarith only [sq_nonneg (x+1/2)]

  · -- the other direction. solve the equation from given range of p.
    -- from discussion above, we claim two solutions are +- √(1/4+p) - 1/2
    rw [Set.encard_eq_two]
    intro hp
    use (√(1/4+p) - 1/2), (-√(1/4+p) - 1/2)
    have h1: 0 < √(1/4+p) := by
      apply Real.sqrt_pos_of_pos ?_
      rcases hp with hp | hp
      <;> linarith only [hp]
    constructor
    · apply ne_of_gt
      linarith only [h1]

    ext x
    set q := x^2+x-p with q_def
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, h_nng1, h_nng2, h_nng3⟩
      specialize q_zero h q_def h_nng1 h_nng2 h_nng3
      rw [q_def] at q_zero
      suffices (x+1/2)^2 = (√(1/4+p))^2 by
        rw [sq_eq_sq_iff_eq_or_eq_neg] at this
        rcases this with hx | hx
        · left
          linarith only [hx]
        · right
          linarith only [hx]
      rw [Real.sq_sqrt (Real.sqrt_pos.mp h1).le]
      linarith only [q_zero]
    · have hh1: 2*p+1-x^2 = (x+1)^2 - 2*q := by
        rw [q_def]
        ring
      have hh2: 3*x+p+4 = (x+2)^2 - q := by
        rw [q_def]
        ring
      have hh3: x^2+9*x+3*p+9 = (2*x+3)^2 - 3*q := by
        rw [q_def]
        ring
      intro xeq
      have qeq: q = 0 := by
        suffices (x+1/2)^2 = 1/4 + p by
          rw [q_def]
          linarith only [this]
        rcases xeq with xeq | xeq
        <;> replace xeq := add_eq_of_eq_sub xeq
        · rw [xeq]
          apply Real.sq_sqrt (Real.sqrt_pos.mp h1).le
        · rw [xeq, neg_sq]
          apply Real.sq_sqrt (Real.sqrt_pos.mp h1).le
      rw [hh1, hh2, hh3, qeq]
      simp only [mul_zero, sub_zero, sq_nonneg, and_self,
      and_true, Real.sqrt_sq_eq_abs]
      rcases hp with hp | hp
      · have h2: √(1/4 + p) ≤ √((1/2)^2) := by
          apply Real.sqrt_le_sqrt ?_
          linarith only [hp.right]
        rw [Real.sqrt_sq (by norm_num)] at h2
        have xge: x ≥ -1 := by
          rcases xeq with xeq | xeq
          <;> rw [xeq] <;> linarith only [h1, h2]
        iterate 3 rw [abs_of_nonneg]
        ring
        all_goals linarith only [xge]
      · have h2: √(1/4+p) ≥ √((3/2)^2) := by
          apply Real.sqrt_le_sqrt ?_
          linarith only [hp]
        rw [Real.sqrt_sq (by norm_num)] at h2
        rcases xeq with xeq | xeq
        · have xge: x ≥ 1 := by
            rw [xeq]
            linarith only [h2]
          iterate 3 rw [abs_of_nonneg]
          ring
          all_goals linarith only [xge]
        · have xle: x ≤ -2 := by
            rw [xeq]
            linarith only [h2]
          iterate 3 rw [abs_of_nonpos]
          ring
          all_goals linarith only [xle]