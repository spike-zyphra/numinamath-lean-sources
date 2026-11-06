import Mathlib

/-
3. The number of triples of positive integers $(x, y, z)$ that satisfy $x y z=3^{2010}$ and $x \leqslant y \leqslant z<x+y$ is $\qquad$.

Answer: 336.
-/

theorem number_theory_303763 :
  { (x, y, z) | x * y * z = 3 ^ 2010 ∧ 0 < x ∧ x ≤ y ∧ y ≤ z ∧ z < x + y}.ncard = 336 := by

  -- We claim that if $k$ is a natural number, then the cardinality of
  -- $T:=\{ (x, y, z) | xyz = 3^k ∧ 0 < x ∧ x \leq y ∧ y \leq z ∧ z < x + y\}$
  -- equals the cardinality of
  -- $S:=\{ (a, b) | a \leq b ∧ a + 2b = k\}.$
  -- The proof is by showing that $f(a,b) ↦ (3^a, 3^b, 3^c)$ is a bijection
  -- from $S$ to $T$.
  have claim1 (k : ℕ) :
      { (x, y, z) : ℕ × ℕ × ℕ | x * y * z = 3 ^ k ∧ 0 < x ∧ x ≤ y ∧ y ≤ z ∧ z < x + y}.ncard
    = { (a, b) : ℕ × ℕ | a ≤ b ∧ a + 2 * b = k}.ncard
       := by
      set S := { (a, b) : ℕ × ℕ | a ≤ b ∧ a + 2 * b = k}
      set T := { (x, y, z) : ℕ × ℕ × ℕ | x * y * z = 3 ^ k ∧ 0 < x ∧ x ≤ y ∧ y ≤ z ∧ z < x + y}

      let f := fun (x : ℕ × ℕ) (h : x ∈ S) ↦ (3 ^ x.1 , 3 ^ x.2, 3 ^ x.2)
      symm
      apply Set.ncard_congr f
      . intro x ⟨ hl, hr ⟩
        simp [f, T]
        constructor
        . simp [← pow_add]
          rw [← hr]
          ring
        . refine Nat.pow_le_pow_of_le ?_ hl
          norm_num
      . intro x y
        simp [f, S]
        aesop
      . simp [S, T]
        intro x y z hxyz
        have : ∃ a b c, x = 3 ^ a ∧ y = 3 ^ b ∧ z = 3 ^ c := by
          have h1 : x ∣ 3 ^ k := by
            use (y * z)
            nlinarith
          rw [Nat.dvd_prime_pow (Nat.prime_three)] at h1
          rcases h1 with ⟨a, ha, hx_eq⟩
          have h2 : y ∣ 3 ^ k := by
            use (x * z)
            nlinarith
          rw [Nat.dvd_prime_pow (Nat.prime_three)] at h2
          rcases h2 with ⟨b, hb, hy_eq⟩
          have h3 : z ∣ 3 ^ k := by
            use (x * y)
            nlinarith
          rw [Nat.dvd_prime_pow (Nat.prime_three)] at h3
          rcases h3 with ⟨c, hc, hz_eq⟩
          have h_eq : 3 ^ a * 3 ^ b * 3 ^ c = 3 ^ k := by
            rw [show 3 ^ a = x by omega, show 3 ^ b = y by omega, show 3 ^ c = z by omega]
            nlinarith
          have h_eq2 : 3 ^ (a + b + c) = 3 ^ k := by
            calc
              3 ^ (a + b + c) = 3 ^ a * 3 ^ b * 3 ^ c := by
                ring_nf
              _ = 3 ^ k := by
                rw [h_eq]
          have h_eq3 : a + b + c = k := by
            exact Nat.pow_right_injective (by norm_num) h_eq2
          exact ⟨a, b, c, by omega, by omega, by omega⟩
        obtain ⟨a, b, c, ⟨hx, hy, hz⟩⟩ := this
        have h_eq : 3 ^ a * 3 ^ b * 3 ^ c = 3 ^ k := by
          rw [show 3 ^ a = x by omega, show 3 ^ b = y by omega, show 3 ^ c = z by omega]
          nlinarith
        rw [← pow_add, ← pow_add] at h_eq
        replace h_eq : a + b + c = k := by
          have : 1 < 3 := by norm_num
          simp [Nat.le_antisymm_iff, Nat.pow_le_pow_iff_right this] at h_eq
          omega
        rw [hx, hy, hz]
        intro h1 h2 h3 h4
        use a, b
        have hab : a ≤ b := by
          by_contra h'
          push_neg at h'
          have g3 : 3 ^ b < 3 ^ a := by
            apply Nat.pow_lt_pow_right
            all_goals omega
          linarith
        have hbc : c = b := by
          rw [Nat.le_antisymm_iff]
          constructor
          . by_contra h'
            simp at h'
            have : 3 ^ a + 3 ^ b < 3 ^ c :=
              calc
                _ ≤ 3 ^ b + 3 ^ b := by gcongr
                _ = 2 * 3 ^ b := by ring
                _ < 3 * 3 ^ b := by gcongr; norm_num
                _ = 3 ^ (b + 1) := by ring
                _ ≤ 3 ^ c := by refine Nat.pow_le_pow_of_le ?_ h'; norm_num
            omega
          . by_contra h'
            push_neg at h'
            have g3 : 3 ^ c < 3 ^ b := by
              apply Nat.pow_lt_pow_right
              all_goals omega
            linarith

        rw [hbc] at h_eq
        rw [add_assoc, ← two_mul] at h_eq
        use ⟨ hab, h_eq ⟩
        simp [f]
        omega

  -- Hence, it suffices to prove that the cardinality of
  -- $\{ (a, b) | a \leq b ∧ a + 2b = 2010\}$ is 336.
  rw [claim1 2010]

  -- Next, we claim that the cardinality of
  -- $S:=\{ (a, b) | a \leq b ∧ a + 2b = 2010\}$
  -- equals the cardinality of
  -- $T:=\{ b | 670 \leq b ∧ b \leq 1005\}$
  -- The proof is by showing that $f(a,b) ↦ b$ is a bijection
  -- from $S$ to $T$.
  have claim2  :
      { (a, b) : ℕ × ℕ | a ≤ b ∧ a + 2 * b = 2010}.ncard
    = { b | 670 ≤ b ∧ b ≤ 1005}.ncard := by
    set S := { (a, b) : ℕ × ℕ | a ≤ b ∧ a + 2 * b = 2010 }
    set T := { b | 670 ≤ b ∧ b ≤ 1005 }
    let f := fun (x : ℕ × ℕ) (h : x ∈ S) ↦ x.2
    apply Set.ncard_congr f
    . intro a ha
      simp [f, T]
      simp [S] at ha
      omega
    . intro p q hp hq
      simp [f]
      simp [S] at hp hq
      intro heq
      have : p.1 = q.1 := by
        rw [heq] at hp
        omega
      exact Prod.ext this heq
    . intro b
      simp [f, S, T]
      intro hlb hub
      use (2010 - 2 * b)
      omega

  -- Hence, it suffices to prove that the cardinality of
  -- $\{ b | 670 \leq b ∧ b \leq 1005\}$ is 336.
  rw [claim2]

  -- But $\{ b | 670 \leq b ∧ b \leq 1005\}$ is a finite set.
  -- Its cardinality is $1005 - 670 + 1 = 336$.
  have claim3 : { b | 670 ≤ b ∧ b ≤ 1005} = Finset.Icc 670 1005 := by
    apply Set.ext
    simp
  rw [claim3]
  rw [Set.ncard_eq_toFinset_card']
  simp