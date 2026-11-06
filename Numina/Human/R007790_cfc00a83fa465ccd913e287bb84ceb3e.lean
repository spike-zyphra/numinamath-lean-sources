import Mathlib

/- Let $S$ be the set of complex numbers of the form $a + bi,$ where $a$ and $b$ are integers.
We say that $z \in S$ is a unit if there exists a $w \in S$ such that $zw = 1.$
Find the number of units in $S.$ -/
theorem algebra_21085 {S : Set ℂ} (hS : S = {z : ℂ | ∃ a b : ℤ, z = a + b * Complex.I}) :
    {z ∈ S | ∃ w ∈ S, z * w = 1}.ncard = 4 := by
  -- if nonnegative integer ab = 1, then a=1 and b=1.
  have lemma_eq_one_of_mul_eq{a b: ℤ}(ha: 0 ≤ a)(hb: 0 ≤ b)
    (heq: a*b = 1): a=1 ∧ b=1 := by
    constructor
    · apply Int.eq_one_of_mul_eq_one_right ha heq
    · apply Int.eq_one_of_mul_eq_one_left hb heq
  -- if zw =1, then |zw| = |z||w|=1, also, |z|^2|w|^2=1
  have h1(z w:ℂ): z*w = 1 → ‖z‖^2*‖w‖^2 = 1 := by
    intro hzw
    have hh1: ‖z*w‖ = 1 := by
      rw [hzw]
      simp
    have hh2: ‖z*w‖ = ‖z‖*‖w‖ := by
      exact NormedField.norm_mul' z w
    have hh3: ‖z‖^2 * ‖w‖^2 = (‖z‖ * ‖w‖)^2 := by
      ring
    rw [hh3, ← hh2, hh1]; simp
  -- if integer (a^2+b^2)(c^2+d^2)=1, then a^2+b^2=c^2+d^2=1
  have h2{a b c d:ℤ}(h: (a^2+b^2)*(c^2+d^2)=1): a^2+b^2=1 ∧ c^2+d^2=1 := by
    apply lemma_eq_one_of_mul_eq ?_ ?_ h
    · linarith [sq_nonneg a, sq_nonneg b]
    · linarith [sq_nonneg c, sq_nonneg d]
  -- and if a^2+b^2=1, then one of a,b must be zero, the other 1 or -1.
  have h3{a b:ℤ}(h:a^2+b^2=1): (a=0 ∧ b=1) ∨ (a=0 ∧ b=-1)
    ∨ (a=1 ∧ b=0) ∨ (a=-1 ∧ b=0) := by
    -- a^2+b^2 = 1, then a^2 = 0 or 1
    have: a^2 = 0 ∨ a^2 = 1 := by
      have hh1: a^2 ≤ 1 := by
        rw [← h]; linarith [sq_nonneg b]
      have hh2 := sq_nonneg a
      interval_cases (a^2); all_goals simp
    rcases this with a0 | a1
    · -- a=0, then b=1
      simp at a0; simp [a0] at h
      simp [a0, h]
    · -- a^2 = 1, a = 1 or -1. b = 0
      simp [a1] at h; simp at a1
      simp [h, a1]
  -- so only four cases. if z ∈ S is a unit, then it can only be 1, -1, i, -i.
  have h4: {z ∈ S | ∃ w ∈ S, z * w = 1} =
    {1, -1, Complex.I, -Complex.I} := by
    -- write |z|^2 in terms of its real part and imaginary part.
    have lemma_normsq{a b:ℤ}: ‖a+b*Complex.I‖^2 = a^2+b^2 := by
      simp
      rw [← Complex.normSq_eq_abs (a+b*Complex.I)]
      rw [Complex.normSq_apply (a+b*Complex.I)]
      have hh1: (a+b*Complex.I).re = a := by simp
      have hh2: (a+b*Complex.I).im = b := by simp
      rw [hh1, hh2]; ring
    ext z; constructor; simp [hS]
    · intro a b hz w c d hw hzw
      -- by h1, zw = 1, then |z|^2 |w|^2 = 1
      -- then according to above lemma, (a^2+b^2)(c^2+d^2) = 1
      -- and by h2, a^2+b^2 = 1, c^2+d^2 = 1.
      obtain ⟨hab, _⟩: a^2+b^2 =1 ∧ c^2+d^2 = 1 := by
        apply h2 ?_
        have := h1 z w hzw
        rw [hz, hw, lemma_normsq, lemma_normsq] at this
        norm_cast at this
      -- by h3, four cases for a,b. a=0,b = 1,-1 ;  b=0, a = 1,-1
      -- substitute z=a+bi, z = 1,-1,i,-i.
      rcases (h3 hab) with hh | hh | hh | hh
      all_goals simp [hz, hh]
    · simp [hS]
      rintro (hz1 | hzn1 | hzi | hzni)
      · -- z=1, z = 1 + 0i, (1+0i) (1+0i) = 1.
        constructor
        · use 1,0; simp [hz1]
        · use 1
          simp [hz1]
          use 1,0; simp
      · -- z=-1 = (-1+0i), (-1+0i)(-1+0i) = 1.
        constructor
        · use (-1),0; simp [hzn1]
        · use (-1)
          simp [hzn1]
          use (-1), 0; simp
      · -- z = i = (0+1i), (0+1i)(0+-1i) = 1.
        constructor
        · use 0, 1; simp [hzi]
        · use -Complex.I
          simp [hzi]
          use 0, -1; simp
      · -- z = -i = (0 + -1i), (0 + -1i)(0 + 1i) = 1.
        constructor
        · use 0, (-1); simp [hzni]
        · use Complex.I
          simp [hzni]
          use 0, 1; simp
  -- obviously, 1,-1,i,-i are pairwise distinct.
  have h5: 1 ≠ Complex.I := by
    have tt1: (Complex.I).re = 0 := by simp
    have tt2: (1:ℂ).re = 1 := by simp
    apply mt Complex.ext_iff.mp
    rw [tt1, tt2]; simp
  have h6: -1 ≠ Complex.I := by
    have tt1: (Complex.I).re = 0 := by simp
    have tt2: (-1:ℂ).re = -1 := by simp
    apply mt Complex.ext_iff.mp
    rw [tt1, tt2]; simp
  have h7: (1:ℂ) ≠ -1 := by
    norm_num
  have h8: (1:ℂ) ≠ -Complex.I := by
    apply mt Complex.ext_iff.mp
    simp
  have h9: Complex.I ≠ -Complex.I := by
    by_contra!; rw [CharZero.eq_neg_self_iff] at this
    have h := Complex.I_ne_zero
    simp [this] at h
  -- therefore four terms in total.
  simp [h4]
  rw [Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem
  , Set.ncard_insert_of_not_mem]; simp
  all_goals simp [h5, h6, h7, h8, h9]