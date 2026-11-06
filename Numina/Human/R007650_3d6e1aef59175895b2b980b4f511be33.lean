import Mathlib

/-How many perfect squares divide 10 ^ 10-/

theorem number_theory_609585: {n: ℕ | 1 ≤ n ∧ ∃ m: ℕ, n = m ^ 2 ∧ n ∣ 10 ^ 10}.encard = 36 := by
  -- first decompose 10 ^ 10 --
  have deup: 10 ^ 10 = 2^10 * 5^10 := by omega
  let x:= 10 ^ 10
  have hx: 10 ^ 10 = x := by simp [x]

-- Use the conditions to simplify the set --
  have set_eq: {n: ℕ |  1 ≤ n ∧ ∃ m: ℕ, n = m ^ 2 ∧ n ∣ 10 ^ 10}
  = {n: ℕ | ∃ m: ℕ, 1 ≤ m ∧ n = m ^ 2 ∧ m ∣ 10 ^ 5} := by
    ext n
    constructor
    -- the forward direction --
    . intro h
      rw [hx] at h
      simp at h
      rcases h with ⟨hn, sq_n, h⟩
      obtain ⟨m, eq⟩ := sq_n
      simp
      use m
      constructor
      . nlinarith
      . constructor
        . omega
        . rw [eq] at h
          simp only [x] at h
          rw [show 10 ^ 10 = (10 ^ 5) ^ 2 by ring] at h
          rw [Nat.pow_dvd_pow_iff] at h
          simp at h
          exact h
          omega
    -- the backward direction --
    . simp
      intro m
      intro bm
      intro sq_n
      intro h
      constructor
      . nlinarith
      . constructor
        . use m
        . rw [sq_n]
          rw [show 10000000000 = 100000 ^ 2 by omega]
          rw [Nat.pow_dvd_pow_iff]
          exact h
          omega
  -- turn the set into a simplied set --
  rw [set_eq]

  -- now turn the encard into a easy one --
  have card_eq: {n: ℕ | ∃ m: ℕ, 1 ≤ m ∧ n = m ^ 2 ∧ m ∣ 10 ^ 5}.encard = {m: ℕ | 1 ≤ m ∧ m ∣ 10 ^ 5}.encard := by
   -- simplify the notation --
    let A:= {n: ℕ | ∃ m: ℕ, 1 ≤ m ∧ n = m ^ 2 ∧ m ∣ 10 ^ 5}
    have hA: {n: ℕ | ∃ m: ℕ, 1 ≤ m ∧ n = m ^ 2 ∧ m ∣ 10 ^ 5} = A:= by simp [A]
    let B:= {m: ℕ | 1 ≤ m ∧ m ∣ 10 ^ 5}
    have hB: {m: ℕ | 1 ≤ m ∧ m ∣ 10 ^ 5} = B:= by simp [B]
    rw [hA]; rw [hB]
   -- define the bijctive map --
    let f :ℕ → ℕ := fun m => m ^ 2
   -- show the bijectivity --
    have f_bij: Set.InjOn f B := by
      simp[Set.InjOn]
      intro b hb
      intro c hc
      simp [f]

    have h:= Set.InjOn.encard_image f_bij
    -- show that A is indeed the image of B --
    have set_eq_image: A = f '' B := by
      ext a
      constructor
      -- A ⊆ f '' B --
      . intro ha
        simp [f]
        simp [A] at ha
        obtain ⟨m, hm, h⟩ := ha
        use m
        simp [B]
        constructor
        . simp [hm]
          omega
        . omega
      -- f '' B ⊆ A --
      . intro ha
        simp [A]
        simp [B] at ha
        obtain ⟨m, hm, h⟩ := ha
        simp [f] at h
        use m
        simp [hm]
        omega
    rw [set_eq_image]
    exact h

 -- now use card_eq to simplify the target --
  rw [card_eq]

  -- Finally, we show that the set is indeed the set of divisors of 10 ^ 5 --
  have card_eq2: {m: ℕ | 1 ≤ m ∧ m ∣ 10 ^ 5} = ((10 ^ 5).divisors: Set ℕ) := by
    ext m
    constructor
    -- the forward direction --
    . intro hm
      simp at hm
      rcases hm with ⟨hm, h⟩
      simp
      exact h
    -- the backward direction --
    . intro hm
      simp at hm
      simp
      constructor
      . by_contra! no
        replace no: m = 0 := by omega
        rw [no] at hm
        tauto
      . exact hm

  rw [card_eq2]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide