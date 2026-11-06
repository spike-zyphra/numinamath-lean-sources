import Mathlib

/-Find the number of sequences a1,..,a10 of positive integers with the property that
a (n+2) = a (n+1) + a n for n = 1,..8, and a 10 = 2002-/

-- present all possible sequences
def a1: ℕ → ℤ
    | 0 => -77
    | 1 => 84
    | n + 2 => a1 (n + 1) + a1 n
def a2: ℕ → ℤ
    | 0 => -22
    | 1 => 50
    | n + 2 => a2 (n + 1) + a2 n
def a3: ℕ → ℤ
    | 0 => 33
    | 1 => 16
    | n + 2 => a3 (n + 1) + a3 n

theorem algebra_611053: {(x,y): ℤ × ℤ | ∃ a: ℕ → ℤ, a 1 = x ∧ a 2 = y ∧ a 10 = 2002 ∧
(∀ n, a (n + 2) = a (n + 1) + a n) ∧ (∀ n: ℕ, 1 ≤ n → 0 < a n)}.encard = 3 := by
-- we directly compute all possible a1 and a2
  have h_eq: {(x,y): ℤ × ℤ | ∃ a: ℕ → ℤ, a 1 = x ∧ a 2 = y ∧ a 10 = 2002 ∧
(∀ n, a (n + 2) = a (n + 1) + a n) ∧ (∀ n: ℕ, 1 ≤ n → 0 < a n)} = {(84,7),(50,28),(16,49)} := by
    ext ⟨x,y⟩
    constructor
    -- first we need to show that the set is a subset of the set
    . intro h
      simp at h
      obtain ⟨a,h⟩ := h
      rcases h with ⟨h1,h2,h3,h4,h5⟩
      simp
      have hx:= h5 1
      simp at hx
      rw [h1] at hx
      have hy:= h5 2
      simp at hy
      rw [h2] at hy
      clear h5
      -- we compute a 10 directly
      have f10: a 10 = 21 * x + 34 * y := by
        have f3:= h4 1
        simp at f3
        have f4:= h4 2
        simp at f4
        have f5:= h4 3
        simp at f5
        have f6:= h4 4
        simp at f6
        have f7:= h4 5
        simp at f7
        have f8:= h4 6
        simp at f8
        have f9:= h4 7
        simp at f9
        have f10:= h4 8
        simp at f10
        nlinarith
      rw [h3] at f10
      clear h1 h2 h3 h4
      -- we first note that 7 ∣ y
      have g: 7 ∣ y := by
        have g1: 7 ∣ 34 * y := by
          rw [show 34 * y = 2002 - 21 * x by omega]
          have g2: 7 ∣ 2002 := by
           norm_num
          have g3: 7 ∣ 21 * x := by
            rw [show 21 * x = 7 * (3 * x) by ring]
            omega
          omega
        have g2: IsCoprime (7: ℤ) 34 := by
          norm_num
        apply IsCoprime.dvd_of_dvd_mul_left g2 g1
      apply exists_eq_mul_right_of_dvd at g
      obtain ⟨k,hk⟩ := g
      simp [hk] at f10
      ring_nf at f10
      simp [hk]
      replace hy: 1 ≤ k := by omega
      replace hk: k ≤ 8 := by omega
      interval_cases k
      all_goals omega

    -- then we need to show that a1 a2 and a3 satisfy the condition
    . intro h
      simp at h
      simp
      rcases h with h | h | h
      -- a1
      . simp [h]
        use a1
        simp [a1]
        intro n hn
        induction' n using Nat.strongRecOn with i ih
        . by_cases hi: i < 3
          . interval_cases i
            all_goals simp [a1]
          . replace hi: 3 ≤ i := by omega
            replace hn: 0 < i := by omega
            have ih1:= ih (i - 1)
            have ih2:= ih (i - 2)
            simp [hn,hi] at ih1
            have o1: 1 ≤ i - 1 := by omega
            simp [o1] at ih1
            have o2: 1 ≤ i - 2 := by omega
            simp [o2,hn] at ih2
            set n:= i - 2 with t
            rw [show i - 1 = n + 1 by simp [t]; omega] at ih1
            rw [show i = n + 2 by simp [t]; omega]
            rw [show a1 (n + 2) = a1 (n + 1) + a1 n by simp [a1]]
            omega
      -- a2
      . simp [h]
        use a2
        simp [a2]
        intro n hn
        induction' n using Nat.strongRecOn with i ih
        . by_cases hi: i < 3
          . interval_cases i
            all_goals simp [a2]
          . replace hi: 3 ≤ i := by omega
            replace hn: 0 < i := by omega
            have ih1:= ih (i - 1)
            have ih2:= ih (i - 2)
            simp [hn,hi] at ih1
            have o1: 1 ≤ i - 1 := by omega
            simp [o1] at ih1
            have o2: 1 ≤ i - 2 := by omega
            simp [o2,hn] at ih2
            set n:= i - 2 with t
            rw [show i - 1 = n + 1 by simp [t]; omega] at ih1
            rw [show i = n + 2 by simp [t]; omega]
            rw [show a2 (n + 2) = a2 (n + 1) + a2 n by simp [a2]]
            omega
      -- a3
      . simp [h]
        use a3
        simp [a3]
        intro n hn
        induction' n using Nat.strongRecOn with i ih
        . by_cases hi: i < 3
          . interval_cases i
            all_goals simp [a3]
          . replace hi: 3 ≤ i := by omega
            replace hn: 0 < i := by omega
            have ih1:= ih (i - 1)
            have ih2:= ih (i - 2)
            simp [hn,hi] at ih1
            have o1: 1 ≤ i - 1 := by omega
            simp [o1] at ih1
            have o2: 1 ≤ i - 2 := by omega
            simp [o2,hn] at ih2
            set n:= i - 2 with t
            rw [show i - 1 = n + 1 by simp [t]; omega] at ih1
            rw [show i = n + 2 by simp [t]; omega]
            rw [show a3 (n + 2) = a3 (n + 1) + a3 n by simp [a3]]
            omega
  rw [h_eq]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { native_decide }