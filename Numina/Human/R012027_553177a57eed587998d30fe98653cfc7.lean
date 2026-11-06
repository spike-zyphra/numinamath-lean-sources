import Mathlib


/- Let $a,b, c$ denote the real numbers such that $1 \le  a, b, c\le  2$.
Consider $T = (a - b)^{2018} + (b - c)^{2018} + (c - a)^{2018}$.
Determine the largest possible value of $T$. -/
theorem inequalities_72276 :
    IsGreatest {x | ∃ a b c : ℝ, 1 ≤ a ∧ a ≤ 2 ∧ 1 ≤ b ∧ b ≤ 2 ∧ 1 ≤ c ∧ c ≤ 2 ∧
    x = (a - b) ^ 2018 + (b - c) ^ 2018 + (c - a) ^ 2018} 2 := by

  -- if k is even, then (x-y)^k = (y-x)^k
  have pow_sub_comm {k:ℕ} (heven: Even k) (x y: ℝ):
    (x - y)^k = (y - x)^k := by
    have: (y-x) = (-1) * (x-y) := by ring
    rw [this, mul_pow, heven.neg_one_pow, one_mul]


  rw [IsGreatest, upperBounds]
  simp only [exists_and_left, Set.mem_setOf_eq,
  forall_exists_index, and_imp]

  constructor
  · -- reach 2 when two of a-b,b-c,c-a is 1, and the other is 0.
    refine ⟨1,?_,?_,1,?_,?_,2,?_,?_,?_⟩
    <;> norm_num

  · -- we may suppose a ≤ b ≤ c
    rintro _ a age ale b bge ble c cge cle rfl
    wlog habc: a ≤ b ∧ b ≤ c
    · have heven: Even 2018 := Nat.even_iff.mpr rfl
      generalize 2018 = k at this heven ⊢
      specialize this pow_sub_comm
      specialize pow_sub_comm heven
      push_neg at habc
      by_cases aleb: a ≤ b
      · by_cases clea: c ≤ a
        · specialize this c cge cle a age ale b bge ble
            ⟨clea, aleb⟩
          refine le_trans (le_of_eq ?_) this
          ring
        · push_neg at clea
          specialize this a age ale c cge cle
            b bge ble ⟨clea.le, (habc aleb).le⟩
          refine le_trans (le_of_eq ?_) this
          rw [pow_sub_comm a b, pow_sub_comm b c,
          pow_sub_comm c a]
          ring
      · push_neg at aleb
        by_cases alec: a ≤ c
        · specialize this b bge ble a age ale
            c cge cle ⟨aleb.le, alec⟩
          refine le_trans (le_of_eq ?_) this
          rw [pow_sub_comm a b, pow_sub_comm b c,
          pow_sub_comm c a]
          ring
        · push_neg at alec
          by_cases cleb: c ≤ b
          · specialize this c cge cle b bge ble
              a age ale ⟨cleb, aleb.le⟩
            refine le_trans (le_of_eq ?_) this
            rw [pow_sub_comm a b, pow_sub_comm b c,
            pow_sub_comm c a]
            ring
          · push_neg at cleb
            specialize this b bge ble c cge cle
              a age ale ⟨cleb.le, alec.le⟩
            refine le_trans (le_of_eq ?_) this
            rw [pow_sub_comm c a]
            ring

    · have: Even 2018 := Nat.even_iff.mpr rfl
      specialize pow_sub_comm this
      rw [pow_sub_comm a b, pow_sub_comm b c]

      -- (b-a)^2018 + (c-b)^2018 ≤ (c-a)^2018,
      -- and 2 (c-a)^2018 ≤ 2 x 1 = 2
      have h1: (b-a)^2018 + (c-b)^2018 ≤
        (c-a)^2018 := by
        replace: c-a = b-a + (c-b) := by ring
        rw [this]
        apply pow_add_pow_le
        <;> linarith only [habc]
      have h2: (c-a)^2018 ≤ 1^2018 := by
        apply (pow_le_pow_iff_left₀ ?_ ?_ ?_).mpr ?_
        <;> linarith only [habc, age, cle]
      simp only [one_pow] at h2
      generalize 2018 = k at h1 h2 ⊢
      linarith only [h1,h2]