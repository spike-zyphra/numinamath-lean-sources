import Mathlib

open scoped BigOperators

/-- a) Prove that there doesn't exist sequence  $a_1,a_2,a_3,... \in \mathbb{N}$  such that:
-- $\forall i < j$ : (a_i+j,a_j+i)=1 -/
theorem number_theory_8793_1 :
  ¬ ∃ a : ℕ → ℕ, ∀ i j, i < j → Nat.gcd (a i + j) (a j + i) = 1 := by
    -- assume there exist such sequence in  $N$ .
    intro ⟨a, ha⟩
    have aux1 : ∀ a b : ℕ, Even a → a.gcd b = 1 → Odd b := by
      intro a b evena hab
      by_contra! evenb
      simp at evenb
      have := hab ▸ Nat.dvd_gcd (even_iff_two_dvd.mp evena) (even_iff_two_dvd.mp evenb)
      tauto
    have aux2 : ∀ a b : ℕ, Even b → a.gcd b = 1 → Odd a := by
      intro a b evenb hab
      rw [Nat.gcd_comm] at hab
      exact aux1 b a evenb hab
    -- Case 1 : $a_1$  is even.
    rcases Nat.even_or_odd (a 1) with evena1 | odda1
    · -- an Auxiliary lemma : if $a_1$  is even, for any postive even number $j$,
      -- `a j` is also even.
      have h1 : ∀ j, j ≠ 0 → Even j → Even (a j) := by
        intro j jpos evenj
        have h1 : 1 < j := by
          have : 1 ≠ j := fun h => ((show ¬ Even 1 by decide) <| h ▸ evenj)
          omega
        have h2 := ha 1 j h1
        have h3 : Odd (a j + 1) := by
          have h3 : Even (a 1 + j) := by exact Even.add evena1 evenj
          exact aux1 (a 1 + j) (a j + 1) h3 h2
        exact (Nat.even_sub' (show 1 ≤ a j + 1 by omega)).2 (by simp [h3])
      -- use the above lemma we have $a_2$ is even and $a_4$ is even.
      obtain ⟨m, hm⟩ := h1 2 (by omega) (by decide)
      obtain ⟨n, hn⟩ := h1 4 (by omega) (by decide)
      have c1 := ha 2 4 (by decide)
      -- then  $gcd(a_2+4, a_4+2)\neq 1$ . Hence contradiction.
      have h2 : 2 ∣ a 2 + 4 := ⟨m + 2, by omega⟩
      have h4 : 2 ∣ a 4 + 2 := ⟨n + 1, by omega⟩
      have := c1 ▸ Nat.dvd_gcd h2 h4
      tauto
    -- Case 2 : $a_1$ is odd.
    · -- $a_1$  is odd then  $gcd(a_1+3,a_{3}+1)=1$, so  $a_{3}$ is even.
      have even3 : Even (a 3) := by
        have := ha 1 3 (by omega)
        have : Odd (a 3 + 1) := by
          have h1 : Even (a 1 + 3) := Nat.even_add'.mpr (by simp [odda1]; decide)
          exact aux1 (a 1 + 3) (a 3 + 1) h1 this
        obtain ⟨k, hk⟩ := this
        exact ⟨k, by omega⟩
      -- $a_3$  is even then  $gcd(a_2+3,a_{3}+2)=1$, so  $a_{2}$ is even.
      have even2 : Even (a 2) := by
        have := ha 2 3 (by omega)
        have h1 : Even (a 3 + 2) := by refine Nat.even_add.mpr (by simpa)
        have h2 := aux2 (a 2 + 3) (a 3 + 2) h1 this
        exact (Nat.even_sub' (show 3 ≤ a 2 + 3 by omega)).2 (by simp [h2]; decide)
      -- $a_3$  is even then  $gcd(a_3+4,a_{4}+3)=1$, so  $a_{4}$ is even.
      have even4 : Even (a 4) := by
        have := ha 3 4 (by omega)
        have h1 : Even (a 3 + 4) := Nat.even_add.2 (by simp [even3]; decide)
        have h2 := aux1 (a 3 + 4) (a 4 + 3) h1 this
        exact (Nat.even_sub' (show 3 ≤ a 4 + 3 by omega)).2 (by simp [h2]; decide)
      -- But then $gcd(a_2+4,a_{4}+2)=1$, contradiction. So No such sequence exist.
      have h := ha 2 4 (by omega)
      have := aux1 (a 2 + 4) (a 4 + 2) (Nat.even_add.2 (by simp [even2]; decide)) h
      have odda4 : Odd (a 4) := (Nat.odd_sub (show 2 ≤ a 4 + 2 by omega)).2 (by simp [this])
      exact Nat.not_odd_iff_even.2 even4 odda4

/--  b) Let  $p$  be an odd prime number.
Prove that there exist sequence  $a_1,a_2,a_3,... \in \mathbb{N}$  such that:
 $\forall i < j: p \not | gcd(a_i+j,a_j+i)$. -/
theorem number_theory_8793_2 {p : ℕ} (hp : Odd p) (hp1 : Nat.Prime p) :
  ∃ a : ℕ → ℕ, ∀ i j, 0 < i → i < j → ¬ p ∣ Nat.gcd (a i + j) (a j + i) := by
    -- let $a_i = ip + 1 - i$.
    use (fun i => i * p + 1 - i)
    -- assume $p \mid gcd(a_i + j, a_j + i)$.
    intro i j ipos hij h
    -- so $p \mid ip + 1 - i + j$ and $p \mid jp + 1 -j + i$.
    have h1 := Nat.dvd_gcd_iff.1 h
    -- Because $p \mid ip + 1 - i + j$, we have `i - j ≡ 1 [ZMOD p] `.
    have h2 : i - j ≡ 1 [ZMOD p] := by
      apply Int.modEq_of_dvd
      rw [←sub_add]
      zify at h1
      rw [Nat.cast_sub] at h1
      simp at h1
      convert Int.dvd_sub h1.1 (show (p : ℤ) ∣ i * p from Int.dvd_mul_left ↑i ↑p) using 1
      ring
      exact le_of_lt (( (Nat.lt_mul_iff_one_lt_right (by omega)).mpr (
        Nat.Prime.one_lt hp1)).trans (by omega))
    -- Because $p \mid jp + 1 -j + i$, we have `i - j ≡ -1 [ZMOD p] `.
    have h3 : i - j ≡ -1 [ZMOD p] := by
      apply Int.modEq_of_dvd
      rw [←Int.dvd_neg]
      simp
      zify at h1
      nth_rw 2 [Nat.cast_sub] at h1
      simp at h1
      convert Int.dvd_sub h1.2 (show (p : ℤ) ∣ j * p from Int.dvd_mul_left j p) using 1
      ring
      exact le_of_lt (( (Nat.lt_mul_iff_one_lt_right (by omega)).mpr (
        Nat.Prime.one_lt hp1)).trans (by omega))
    -- So we have `-1 ≡ 1 [ZMOD ↑p]`, i.e. $p \mid 2$. However, $p$ is an odd prime number.
    -- Hence, we reach a contradiction.
    have := h3.symm.trans h2
    have := Int.ModEq.dvd this
    simp at this
    norm_cast at this
    have := Nat.le_of_dvd (by omega) this
    have : 2 ≤ p := by exact Nat.Prime.two_le hp1
    have : p ≠ 2 := fun h => (by have := h ▸ hp; tauto)
    omega
