import Mathlib

/-How many numbers between 1 and 1,000,000 are perfect squares but not perfect cubes?-/
theorem number_theory_608401: {x : ℕ | 1 ≤ x ∧ x ≤ 10^6 ∧ (∃ n, x = n^2) ∧ ¬(∃ m, x = m^3)}.encard = 990 := by

  -- First compute the number of perfect squares between 1 and 10^6 --
  have h_squares : {x : ℕ | 1 ≤ x ∧ x ≤ 10^6 ∧ (∃ n, x = n^2)}.encard = 1000 := by
    have h_eq : {x | 1 ≤ x ∧ x ≤ 10^6 ∧ ∃ n, x = n^2} = (Finset.range 1000).image (fun n => (n+1)^2) := by
      ext x
      simp only [Set.mem_setOf_eq, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨h1, h2, n, hn⟩
        simp
        use (n - 1)
        rw [hn]
        constructor
        . rw [hn] at h2
          by_contra! no
          replace no: 1001 ≤ n := by omega
          have contra: 1001 ^ 2 ≤ 10 ^ 6 := by
            calc
              1001 ^ 2 ≤ n ^ 2 := by apply Nat.pow_le_pow_left; exact no
                      _ ≤ 10 ^ 6 := by omega
          tauto
        . have triv: n - 1 + 1 = n := by
            rw [Nat.sub_one_add_one]
            nlinarith
          rw [triv]

      · intro hx
        simp at hx
        obtain ⟨n,hn⟩ := hx
        rcases hn with ⟨bn,h⟩
        constructor
        . rw [← h]
          nlinarith
        . constructor
          . rw [← h]
            nlinarith
          . use (n + 1)
            omega
    -- The cardinality is preserved through this bijection --
    rw [h_eq]    
    rw [Set.encard_coe_eq_coe_finsetCard]
    rw [Finset.card_image_of_injective]
    . simp [Set.Iio]
    . intro x y xy
      simp at xy
      omega


  -- The number of perfect sixth powers (both squares and cubes) is floor (10^6 ^ (1/6)) = 10
  have h_sixth_powers : {x : ℕ | 1 ≤ x ∧ x ≤ 10^6 ∧ (∃ k, x = k^6)}.encard = 10 := by
    -- the proof is similar to the one for squares --
    have h_eq : {x | 1 ≤ x ∧ x ≤ 10^6 ∧ ∃ n, x = n^6} = (Finset.range 10).image (fun n => (n+1)^6) := by
      ext x
      simp only [Set.mem_setOf_eq, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨h1, h2, n, hn⟩
        simp
        use (n - 1)
        rw [hn]
        constructor
        . rw [hn] at h2
          by_contra! no
          replace no: 11 ≤ n := by omega
          have contra: 11 ^ 6 ≤ 10 ^ 6 := by
            calc
              11 ^ 6 ≤ n ^ 6 := by apply Nat.pow_le_pow_left; exact no
                      _ ≤ 10 ^ 6 := by omega
          tauto
        . have triv: n - 1 + 1 = n := by
            rw [Nat.sub_one_add_one]
            rw [hn] at h1
            by_contra! o
            rw [o] at h1
            omega
          rw [triv]

      · intro hx
        simp at hx
        obtain ⟨n,hn⟩ := hx
        rcases hn with ⟨bn,h⟩
        constructor
        . rw [← h]
          calc
            1 = 1 ^ 6 := by norm_num
            _ ≤ (n + 1) ^ 6 := by apply Nat.pow_le_pow_left; omega
        . constructor
          . rw [← h]
            replace bn: n + 1 ≤ 10 := by omega
            apply Nat.pow_le_pow_left
            omega
          . use (n + 1)
            omega
    -- The cardinality is preserved through this bijection --
    rw [h_eq]
    simp [Set.encard]
    rw [Finset.card_image_of_injective]
    . simp [Set.Iio]
    . intro x y xy
      simp at xy
      omega


  -- The number of perfect squares that are not perfect cubes is squares - sixth powers
  have h_sub : {x : ℕ | 1 ≤ x ∧ x ≤ 10^6 ∧ (∃ n, x = n^2) ∧ ¬(∃ m, x = m^3)} =
               {x : ℕ | 1 ≤ x ∧ x ≤ 10^6 ∧ (∃ n, x = n^2)} \
               {x : ℕ | 1 ≤ x ∧ x ≤ 10^6 ∧ (∃ k, x = k^6)} := by
    ext x
    constructor
    . intro hx
      simp at hx
      obtain ⟨bx1, bx2, n, h⟩ := hx
      obtain ⟨n,hn⟩ := n
      simp
      simp [bx1,bx2]
      constructor
      . use n
      . intro y
        specialize h (y ^ 2)
        have eq: (y ^ 2) ^ 3 = y ^ 6 := by
          rw [← Nat.pow_mul]
        rw [eq] at h
        exact h
    . intro hx
      simp at hx
      simp
      rcases hx with ⟨p,q⟩
      rcases p with ⟨bx1,bx2,n⟩
      obtain ⟨n,hn⟩ := n
      simp [bx1,bx2] at q
      simp [bx1,bx2]
      constructor
      . use n
      . intro y
        by_contra! hy
        absurd q
        simp
        clear * - bx1 hy hn
        have hy2:= hy
        rw [hn] at hy
        have h1: y ^ 2 ∣ n ^ 2 := by
          rw [hy]
          apply Nat.pow_dvd_pow
          omega
        have h2: y ∣ n := by
          rw [Nat.pow_dvd_pow_iff] at h1
          exact h1
          omega
        apply exists_eq_mul_right_of_dvd at h2
        obtain ⟨k, hk⟩ := h2
        rw [hk] at hy
        replace hy: y = k ^ 2 := by
          have eq1: (y * k) ^ 2 = y ^ 2 * k ^ 2 := by
            ring_nf
          rw [eq1] at hy
          nlinarith
        simp [hy] at hy2
        rw [← Nat.pow_mul] at hy2
        simp at hy2
        use k

  -- The cardinality of the difference is squares - sixth powers = 1000 - 10 = 990
  rw [h_sub]
  have card_add: ({x : ℕ | 1 ≤ x ∧ x ≤ 10^6 ∧ (∃ n, x = n^2)} \ {x : ℕ | 1 ≤ x ∧ x ≤ 10^6 ∧ (∃ k, x = k^6)}).encard
  + {x : ℕ | 1 ≤ x ∧ x ≤ 10^6 ∧ (∃ k, x = k^6)}.encard = {x : ℕ | 1 ≤ x ∧ x ≤ 10^6 ∧ (∃ n, x = n^2)}.encard := by
    rw [Set.encard_diff_add_encard_of_subset]
    simp
    intro a
    intro ha1
    intro ha2
    intro x
    intro ha
    constructor
    . omega
    . constructor
      . omega
      . use (x ^ 3)
        simp [ha]
        nlinarith
  rw [h_squares, h_sixth_powers] at card_add

  let S:= ({x | 1 ≤ x ∧ x ≤ 10 ^ 6 ∧ ∃ n, x = n ^ 2} \ {x | 1 ≤ x ∧ x ≤ 10 ^ 6 ∧ ∃ k, x = k ^ 6}) -- S is the target set --
  have hS: ({x | 1 ≤ x ∧ x ≤ 10 ^ 6 ∧ ∃ n, x = n ^ 2} \ {x | 1 ≤ x ∧ x ≤ 10 ^ 6 ∧ ∃ k, x = k ^ 6}) = S := by simp [S]
  -- we need to show S is finite --
  have s_fin: Set.Finite S := by
    simp [Set.Finite]
    simp [S]
    have subset: S ⊆ (Finset.Icc 1 1000000 : Set ℕ) := by
      have subset1: S ⊆ {x | 1 ≤ x ∧ x ≤ 10 ^ 6 ∧ ∃ n, x = n ^ 2} := by
        simp [S]
        apply Set.diff_subset
      have subset2: {x | 1 ≤ x ∧ x ≤ 10 ^ 6 ∧ ∃ n, x = n ^ 2} ⊆ (Finset.Icc 1 1000000 : Set ℕ) := by
        intro x
        intro hx
        simp at hx
        simp
        simp [hx]
      apply Set.Subset.trans subset1 subset2

    have fin: Set.Finite (Finset.Icc 1 1000000 : Set ℕ) := by
      apply Finset.finite_toSet
    apply Set.Finite.subset fin subset

  let A:= S.encard
  have A_ne_t: A ≠ ⊤ := by
    by_contra! A_t
    simp [A] at A_t
    tauto
  have hA: S.encard = A:= by simp [A]
  simp only [hA,S] at card_add
  simp only [hS,hA]
  clear_value A
  clear * - card_add A_ne_t

  -- we are done almostly, but we need to tackle with ⊤, hence it takes a bit of time --
  rw [ENat.ne_top_iff_exists] at A_ne_t
  obtain ⟨a, ha⟩ := A_ne_t
  rw [←ha] at card_add
  rw [←ha]
  clear ha
  have h10 : (10 : ℕ∞) = ↑(10 : ℕ) := by rfl
  rw [h10] at card_add
  rw [← Nat.cast_add] at card_add
  have h1000 : (1000 : ℕ∞) = ↑(1000 : ℕ) := by rfl
  rw [h1000] at card_add
  rw [ENat.coe_inj] at card_add
  have ha: a = 990 := by
    omega
  have h990:  (990 : ℕ∞) = ↑(990 : ℕ) := by rfl
  rw [h990]
  rw [ENat.coe_inj]
  omega