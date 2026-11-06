import Mathlib

/-The set P consisting of certain integers has the following properties: (1) P contains both positive and negative numbers;
(2) P contains both odd and even numbers;
(3) 1 ∉ P
(4) If x,y∈P, then x+y∈P.
Determine the relationship between 0, 2 and the set P.-/

theorem number_theory_206913 {P: Set ℤ} (h1: ∃ x y: ℤ, x < 0 ∧ 0 < y ∧
  x ∈ P ∧ y ∈ P) (h2: ∃ m n: ℤ, Odd m ∧ Even n ∧ m ∈ P ∧ n ∈ P) (h3: 1 ∉ P)
  (h4: ∀ x y: ℤ, x ∈ P → y ∈ P → x + y ∈ P): 0 ∈ P ∧ 2 ∉ P := by

  -- set a and b the least positive and greatest negative elements of P
  set a:= -sSup {x | x < 0 ∧ -x ∈ P}
  set b:= sSup {x | x < 0 ∧ x ∈ P}

  have f1: -a ∈ {x | x < 0 ∧ -x ∈ P} ∧ ∀ y ∈ {x | x < 0 ∧ -x ∈ P}, y ≤ -a := by
    set s:= {x | x < 0 ∧ -x ∈ P}
    have i: BddAbove s := by
      use 0
      intro y ly
      simp [s] at ly
      omega
    have h: sSup s = -a := by
      simp [a, s]
    constructor
    .
      rw [← h]
      apply Int.csSup_mem
      obtain ⟨x, y, hx, hy, hpx, hpy⟩ := h1
      use -y
      simp [s]
      constructor
      .
        omega
      .
        exact hpy
      tauto
    .
      rw [← h]
      intro y sy
      apply le_csSup_of_le i sy (by simp)


  have g1: b ∈ {x | x < 0 ∧ x ∈ P} ∧ ∀ y ∈ {x | x < 0 ∧ x ∈ P}, y ≤ b := by
    set s:= {x | x < 0 ∧ x ∈ P}
    have i: BddAbove s := by
      use 0
      intro y ly
      simp [s] at ly
      omega
    have h: sSup s = b := by
      simp [b, s]
    constructor
    .
      rw [← h]
      apply Int.csSup_mem
      obtain ⟨x, y, hx, hy, hpx, hpy⟩ := h1
      use x
      simp [s]
      constructor
      .
        omega
      .
        exact hpx
      tauto
    .
      rw [← h]
      intro y sy
      apply le_csSup_of_le i sy (by simp)
  rcases f1 with ⟨f1, f2⟩
  rcases g1 with ⟨g1, g2⟩
  simp at f1
  rcases f1 with ⟨ha, f1⟩
  rcases g1 with ⟨hb, g1⟩

  have h5: a + b ∈ P := by
    exact h4 a b f1 g1

  -- we show that a + b = 0
  have h6: a + b = 0 := by
    have l1: b < a + b := by
      omega
    have l2: a + b < a := by
      omega
    by_contra! u
    by_cases l: a + b < 0
    -- if a + b < 0
    .
      specialize g2 (a + b)
      absurd l1
      simp
      simp at g2
      apply g2
      exact l
      exact h5
    -- if a + b ≥ 0
    .
      replace l: 0 < a + b := by
        omega
      specialize f2 (-(a + b))
      absurd l2
      simp
      simp at f2
      apply f2
      linarith
      exact h5

  simp [h6] at h5
  simp [h5]

  -- to show 2 ∉ P, we prove by contradiction
  by_contra! h7

  -- we first show that a = 2 indeed
  replace ha: a = 2 := by
    specialize f2 (-2)
    simp [h7] at f2
    have o: a ≠ 1 := by
      by_contra! o
      simp [o] at f1
      trivial
    omega
  simp [ha] at *

  -- then b must be -2
  replace hb: b = -2 := by
    omega
  simp [hb] at *

  -- then we show that any even number is in P
  have h8: ∀ k: ℕ, (2 * (k: ℤ)) ∈ P ∧ (-2 * (k: ℤ)) ∈ P := by
    intro k
    induction' k with k ih
    .
      simp
      tauto
    .
      rcases ih with ⟨ih1, ih2⟩
      constructor
      .
        have o: 2 * ↑(k + (1: ℕ)) = 2 * (k: ℤ) + 2 := by
          norm_cast
        rw [o]
        clear o
        specialize h4 (2 * (k: ℤ)) 2 ih1 h7
        exact h4
      .
        have o: -2 * ↑(k + (1: ℕ)) = -2 * (k: ℤ) - 2 := by
          norm_cast
          simp
          ring
        rw [o]
        clear o
        specialize h4 (-2 * (k: ℤ)) (-2) ih2 g1
        simp at h4
        simp
        exact h4
  obtain ⟨m, hm, n, hn, sm, sn⟩ := h2
  clear hn sn
  apply Odd.exists_bit1 at hm
  obtain ⟨t, hm⟩ := hm

  -- then we have 1 ∈ P, which is a contradiction
  specialize h8 t.natAbs
  by_cases r: 0 ≤ t
  .
    simp at h8
    rw [show |t| = t by apply abs_of_nonneg r] at h8
    rcases h8 with ⟨h8, h9⟩
    rw [hm] at sm
    specialize h4 (2 * t + 1) (-(2 * t)) sm h9
    simp at h4
    tauto
  .
    simp at r
    simp at h8
    rw [show |t| = -t by apply abs_of_neg r] at h8
    rcases h8 with ⟨h8, h9⟩
    rw [hm] at sm
    specialize h4 (2 * t + 1) (2 * (-t)) sm h8
    simp at h4
    tauto