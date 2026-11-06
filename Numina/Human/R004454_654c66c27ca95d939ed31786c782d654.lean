import Mathlib

-- 14. The set $P$ consisting of certain integers has the following properties:
-- (1) $P$ contains both positive and negative numbers;
-- (2) $P$ contains both odd and even numbers;
-- (3) $1 \notin P$;
-- (4) If $x, y \in P$, then $x+y \in P$.
-- Determine the relationship between 0, 2 and the set $P$.
-- 14. $0 \in P, 2 \notin P$.

-- Solution: Let $a$ be the smallest positive number in $P$, and $b$ be the largest negative number in $P$. Then $b < a+b < a$, and $a+b \in P$. Since $a+b$ is neither positive nor negative, we have $a+b=0$, i.e., $0 \in P$. Since $1 \notin P$, we have $a \geqslant 2$. From $a+b=0 \Rightarrow a=-b$, we get $b \leqslant-2$. If $a=2$, then $b=-2$. By repeatedly using condition (4), we get $\pm 2k \in P$ for $k \in \mathbf{N}$. Since $P$ contains odd numbers, let $m=2t+1 \in P$. Combined with $-2t \in P$, we get $1 \in P$, which is a contradiction. Therefore, $2 \notin P$. In conclusion, $0 \in P$ and $2 \notin P$.

lemma sInf_lemma (P : Set ℕ) (hP : P.Nonempty): ∃ a, a ∈ P ∧ ∀ x ∈ P, a ≤ x := by
  use sInf P
  constructor
  · exact Nat.sInf_mem hP
  · intro x hx
    exact Nat.sInf_le hx

theorem number_theory_269084
  (P : Set ℤ) (hP : ∀ x ∈ P, ∀ y ∈ P, x + y ∈ P)
  (hP1 : ∃ x ∈ P, x > 0) (hP2 : ∃ x ∈ P, x < 0) (hP3 : ∃ x ∈ P, Odd x)
  (hP4 : ∃ x ∈ P, Even x) (hP5 : 1 ∉ P) :
  0 ∈ P ∧ 2 ∉ P := by

  let P_pos := {x : ℤ | x ∈ P ∧ x > 0}
  let P_neg := {x : ℤ | x ∈ P ∧ x < 0}

  -- Both sets are non-empty
  have pos_nonempty : P_pos.Nonempty := by
    obtain ⟨x, hx_mem, hx_pos⟩ := hP1
    exact ⟨x, hx_mem, hx_pos⟩

  have neg_nonempty : P_neg.Nonempty := by
    obtain ⟨x, hx_mem, hx_neg⟩ := hP2
    exact ⟨x, hx_mem, hx_neg⟩

  have ⟨a, ha_mem_P, ha_pos, ha_min⟩ : ∃ a, a ∈ P ∧ a > 0 ∧ ∀ x ∈ P, x > 0 → a ≤ x := by
    -- Define the set of natural numbers corresponding to positive integers in P
    let P_nat := {n : ℕ | (n : ℤ) ∈ P ∧ n > 0}

    -- Prove that P_nat is non-empty
    have hP_nat_nonempty : P_nat.Nonempty := by
      obtain ⟨x, hx_mem, hx_pos⟩ := hP1
      use x.natAbs
      constructor
      · rw [Int.natAbs_of_nonneg (le_of_lt hx_pos)]
        exact hx_mem
      · exact Int.natAbs_pos.mpr (ne_of_gt hx_pos)

    -- Use the lemma to find the minimal element in P_nat
    obtain ⟨a_nat, ha_nat_mem, ha_nat_min⟩ := sInf_lemma P_nat hP_nat_nonempty

    -- Convert the result back to integers
    use a_nat
    constructor
    · -- Prove a_nat ∈ P
      simp [P_nat] at ha_nat_mem
      exact ha_nat_mem.1
    constructor
    · -- Prove a_nat > 0
      simp [P_nat] at ha_nat_mem
      exact Nat.cast_pos.mpr ha_nat_mem.2
    · -- Prove a_nat is minimal
      intro x hx_mem hx_pos
      -- Convert x to a natural number
      have hx_nat_in : x.natAbs ∈ P_nat := by
        constructor
        · rw [Int.natAbs_of_nonneg (le_of_lt hx_pos)]
          exact hx_mem
        · exact Int.natAbs_pos.mpr (ne_of_gt hx_pos)
      -- Use the minimality from the lemma
      have := ha_nat_min x.natAbs hx_nat_in
      -- Convert back to integer inequality
      have h_eq : x = ↑(x.natAbs) := by
        exact (Int.natAbs_of_nonneg (le_of_lt hx_pos)).symm
      rw [h_eq]
      exact Nat.cast_le.mpr this


  have ⟨b, hb_mem_P, hb_neg, hb_max⟩ : ∃ b, b ∈ P ∧ b < 0 ∧ ∀ x ∈ P, x < 0 → x ≤ b := by
    -- Define the set of natural numbers corresponding to negative integers in P (taking negation)
    let P_neg_nat := {n : ℕ | (-↑n : ℤ) ∈ P ∧ n > 0}

    -- Prove that P_neg_nat is non-empty
    have hP_neg_nat_nonempty : P_neg_nat.Nonempty := by
      obtain ⟨x, hx_mem, hx_neg⟩ := hP2
      use (-x).natAbs
      constructor
      · have h_pos : -x > 0 := by linarith [hx_neg]
        rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
        simp
        exact hx_mem
      · exact Int.natAbs_pos.mpr (by linarith [hx_neg])

    -- Use the lemma to find the minimal element in P_neg_nat
    obtain ⟨b_nat, hb_nat_mem, hb_nat_min⟩ := sInf_lemma P_neg_nat hP_neg_nat_nonempty

    -- Convert the result back to negative integers
    use -↑b_nat
    constructor
    · -- Prove -b_nat ∈ P
      simp [P_neg_nat] at hb_nat_mem
      exact hb_nat_mem.1
    constructor
    · -- Prove -b_nat < 0
      simp [P_neg_nat] at hb_nat_mem
      exact neg_neg_iff_pos.mpr (Nat.cast_pos.mpr hb_nat_mem.2)
    · -- Prove -b_nat is the largest negative number
      intro x hx_mem hx_neg
      -- Convert x to the corresponding natural number
      have hx_neg_nat_in : (-x).natAbs ∈ P_neg_nat := by
        constructor
        · have h_pos : -x > 0 := by linarith [hx_neg]
          rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
          simp
          exact hx_mem
        · exact Int.natAbs_pos.mpr (by linarith [hx_neg])
      -- Use the minimality from the lemma
      have := hb_nat_min (-x).natAbs hx_neg_nat_in
      -- Convert back to integer inequality
      have h_eq_x : x = -(↑((-x).natAbs)) := by
        have h_pos : -x > 0 := by linarith [hx_neg]
        rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
        simp
      rw [h_eq_x]
      exact neg_le_neg (Nat.cast_le.mpr this)

  -- Now a + b ∈ P by closure
  have hab_in_P : a + b ∈ P := hP a ha_mem_P b hb_mem_P

  -- Key claim: a + b = 0
  have hab_eq_zero : a + b = 0 := by
    -- We show a + b can be neither positive nor negative
    by_contra h_ne_zero
    cases' lt_or_gt_of_ne h_ne_zero with h_neg h_pos
    · -- Case: a + b < 0
      -- Then a + b is a negative element of P
      -- But a + b > b (since a > 0), contradicting maximality of b
      have h_b_lt_ab : b < a + b := by linarith [ha_pos]
      have h_ab_le_b : a + b ≤ b := hb_max (a + b) hab_in_P h_neg
      linarith [h_b_lt_ab, h_ab_le_b]
    · -- Case: a + b > 0
      -- Then a + b is a positive element of P
      -- But a + b < a (since b < 0), contradicting minimality of a
      have h_ab_lt_a : a + b < a := by linarith [hb_neg]
      have h_a_le_ab : a ≤ a + b := ha_min (a + b) hab_in_P h_pos
      linarith [h_ab_lt_a, h_a_le_ab]

  -- Therefore 0 = a + b ∈ P, contradicting our assumption
  have h_zero_in_P : 0 ∈ P := by
    rw [← hab_eq_zero]
    exact hab_in_P

  refine ⟨h_zero_in_P, ?_⟩

  by_contra h_contra
  have h_a_eq_2 : a = 2 := by
    have := ha_min 2 h_contra (by norm_num)
    interval_cases a
    . contradiction
    . rfl

  have h_b_eq_neg2 : b = -2 := by linarith

  have h_neg2_in_P: -2 ∈ P := by
    rw [h_b_eq_neg2] at hb_mem_P
    exact hb_mem_P

  obtain ⟨n, hn1, hn2⟩ := hP3
  obtain ⟨m, hm⟩ := hn2

  have : - (2 * m) ∈ P := by
    -- We'll use the fact that 2 ∈ P, -2 ∈ P, and 0 ∈ P to generate all even multiples
    have h_even_gen : ∀ k : ℕ, (2 * k : ℤ) ∈ P ∧ (-(2 * k) : ℤ) ∈ P := by
      intro k
      induction k with
      | zero =>
        constructor
        · simp; exact h_zero_in_P
        · simp; exact h_zero_in_P
      | succ k ih =>
        constructor
        · -- 2 * (k + 1) = 2 * k + 2, and both are in P
          have : (2 * (k + 1 : ℕ) : ℤ) = (2 * k : ℤ) + 2 := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring
          rw [this]
          have h_2_in_P : (2 : ℤ) ∈ P := h_contra
          exact hP (2 * k) ih.1 2 h_2_in_P
        · -- -(2 * (k + 1)) = -(2 * k) + (-2), and both are in P
          have : (-(2 * (k + 1 : ℕ)) : ℤ) = (-(2 * k) : ℤ) + (-2) := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring
          rw [this]
          exact hP (-(2 * k)) ih.2 (-2) h_neg2_in_P

    -- Now handle the three cases for m
    by_cases h1 : m = 0
    · simp [h1]; exact h_zero_in_P
    by_cases h2 : m > 0
    · -- m > 0: -(2 * m) is negative, use the negative even generation
      have : ∃ k : ℕ, (m : ℤ) = (k : ℤ) ∧ k > 0 := by
        use m.natAbs
        constructor
        · exact (Int.natAbs_of_nonneg (le_of_lt h2)).symm
        · exact Int.natAbs_pos.mpr (ne_of_gt h2)
      obtain ⟨k, hk_eq, hk_pos⟩ := this
      rw [hk_eq]
      exact (h_even_gen k).2
    · -- m < 0: -(2 * m) is positive, use the positive even generation
      have h_neg : m < 0 := by
        have : m ≤ 0 := le_of_not_gt h2
        exact lt_of_le_of_ne this h1
      have : ∃ k : ℕ, (-m : ℤ) = (k : ℤ) ∧ k > 0 := by
        use (-m).natAbs
        constructor
        · exact (Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt h_neg))).symm
        · exact Int.natAbs_pos.mpr (neg_ne_zero.mpr (ne_of_lt h_neg))
      obtain ⟨k, hk_eq, hk_pos⟩ := this
      have : -(2 * m) = 2 * k := by
        rw [← hk_eq]
        ring
      rw [this]
      exact (h_even_gen k).1

  have h_1_in_P: 1 ∈ P := by
    have := hP n hn1 (- (2 * m)) this
    rw [hm] at this
    norm_num at this
    exact this

  contradiction
