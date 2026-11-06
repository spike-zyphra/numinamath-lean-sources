import Mathlib

/- Task B-2.5. (20 points) Find all solutions to the equation $\lfloor x\rfloor\{x\}=2009 x$, where $\lfloor x\rfloor$ is the greatest integer not greater than $x$, and $\{x\}=x-\lfloor x\rfloor$. -/
theorem number_theory_220047 (x : ℝ) :
    ⌊x⌋ * (x - ⌊x⌋) = 2009 * x ↔ x = 0 ∨ x = -1 / 2010 := by
  -- left is trivial
  constructor
  rotate_left
  · intro h
    cases' h with h h <;> rw [h]; simp
    · suffices ⌊(-1:ℝ) / 2010⌋ = -1 by
        rw [this];
        norm_num
      apply Int.floor_eq_iff.mpr
      constructor
      <;> simp; norm_num
      apply div_neg_of_neg_of_pos <;> norm_num
  intro h
  -- let's analyze by cases depending on the sign of x
  cases' lt_trichotomy x 0 with hn hz
  rotate_left
  cases' hz with hz hp
  · -- this one is trivial
    left; assumption
  · -- ⌊x⌋{X} ≤ ⌊x⌋ ≤ x < x * 2009
    exfalso
    -- let's show {x} < 1
    have h1 := Int.fract_lt_one x
    -- now we proceed to show our contradiction
    have h2 :=
      calc ↑⌊x⌋ * (x - ↑⌊x⌋)
      _ = ⌊x⌋ * (Int.fract x) := by rfl
      _ ≤ ⌊x⌋ * 1 := by gcongr
      _ = ⌊x⌋ := by norm_num
      _ ≤ x := Int.floor_le x
      _ < x * 2009 := by linarith
    linarith
  · -- if x is negative we can write x = -p+α with p:ℕ and α:[0, 1)
    let q:∃ p:ℕ, ∃ α∈ (Set.Ico (0:ℝ) 1), x = -p+α := by
      use (-⌊x⌋).toNat
      use Int.fract x
      constructor
      · constructor
        exact Int.fract_nonneg x
        exact Int.fract_lt_one x
      have h3:=Int.toNat_of_nonneg (a:=-Int.floor x) (by simp; apply Int.floor_nonpos; linarith)
      rify at h3
      rw [h3]
      simp
    obtain ⟨p, ⟨α, ⟨hα, xdef⟩⟩⟩ := q
    rw [xdef] at h;simp at h
    -- let's get rid of floor and fraction
    have: ⌊-(p:ℝ) + α⌋ = -(p:ℤ) := by
      refine Int.floor_eq_iff.mpr ?_
      constructor
      · simp; exact hα.left
      · simp; exact hα.right
    rw [this] at h
    have: Int.fract (-(p:ℝ) + α) = α := by
      refine Int.fract_eq_iff.mpr ?_
      constructor
      exact hα.left
      constructor
      exact hα.right
      use -p
      simp
    rw [this] at h
    simp at h
    -- let's solve for α
    apply congr_arg (fun x => (x - 2009*α)/(-p-2009)) at h
    conv_lhs at h =>
      calc _
      _ = -((p + 2009) * α) / -(p + 2009) := by ring_nf
      _ = α * ((-(p + 2009))/ -(p + 2009)) := by ring_nf
      _ = α := by rw [div_self (by apply ne_of_lt; simp; linarith), mul_one]
    conv_rhs at h =>
      calc _
      _ = (2009 * -p + (2009 * α - 2009 * α)) / (-↑p - 2009) := by ring_nf
      _ = (2009 * -p) / (-p - 2009) := by ring_nf
      _ = -(2009 * p) / -(2009+p) := by ring_nf
      _ = (2009 * p) / (p + 2009) := by rw [neg_div_neg_eq]; ring_nf
    -- since α < 1 we can conclude that 2009*p/(p+2009) < 1
    have hp:=hα.right
    rw [h] at hp
    apply (mul_lt_mul_right (a:=((p:ℝ) + 2009)) (by linarith)).mpr at hp
    rw [one_mul, div_mul, div_self (by linarith), div_one] at hp
    have hp': 2009*(p:ℝ) - p < 2009 := by linarith
    ring_nf at hp'
    have hp'': p < 2009/(2008:ℝ) := by linarith
    -- therefore p must be either 0 or 1
    have hp''': p < 2 := by
      by_contra h
      simp at h
      rify at h
      linarith
    have hp2: p = 0 ∨ p = 1 := by
      refine Nat.le_one_iff_eq_zero_or_eq_one.mp ?_
      omega
    cases' hp2 with hp2 hp2
    · -- p = 0 is not actually possible since it could only occur with x=0, but we are assuming x < 0
      exfalso
      rw [hp2] at h
      norm_num at h
      rw [h, hp2] at xdef; norm_num at xdef; linarith
    -- p = 1 will give the other possible solution
    right
    rw [hp2] at h
    norm_num at h
    rw [h, hp2] at xdef; norm_num at xdef; linarith