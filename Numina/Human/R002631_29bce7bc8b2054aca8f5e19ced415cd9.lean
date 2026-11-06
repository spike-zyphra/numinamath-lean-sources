import Mathlib

open Finset

/-- Call a number prime-looking if it is
[composite](https://artofproblemsolving.com/wiki/index.php/Composite) but not
divisible by $2, 3,$ or $5.$ -/
def Nat.PrimeLooking (n : ℕ) : Bool := n ≠ 1 ∧ ¬n.Prime ∧ ¬(2 ∣ n) ∧ ¬(3 ∣ n) ∧ ¬(5 ∣ n)

/-- Call a number prime-looking if it is
[composite](https://artofproblemsolving.com/wiki/index.php/Composite) but not divisible by $2, 3,$
or $5.$ The three smallest prime-looking numbers are $49, 77$, and $91$. There are $168$ prime
numbers less than $1000$. How many prime-looking numbers are there less than $1000$?
$(\mathrm {A}) \ 100 \qquad (\mathrm {B}) \ 102 \qquad (\mathrm {C})\ 104 \qquad (\mathrm {D}) \
106 \qquad (\mathrm {E})\ 108$ -/
theorem number_theory_1154
    (hPrimesCard : #{n ∈ range 1000 | n.Prime} = 168)
    : #{n ∈ range 1000 | n.PrimeLooking} = 100 := by

  -- We can split the numbers from $0$ to $999$ into several groups:
  -- $\{1\},$ $\{\mathrm{numbers\ divisible\ by\ 2 = S_2}\},$ $\{\mathrm{numbers\ divisible\ by\ 3
  -- = S_3}\},$ $\{\mathrm{numbers\ divisible\ by\ 5 = S_5}\},
  -- \{\mathrm{primes\ not\ including\ 2,3,5}\},$ $\{\mathrm{prime-looking}\}$

  -- Let $S_{N, p}$ be the set of numbers less than $N$ which are divisible by $p$.
  let S (N p : ℕ) := {n ∈ range N | p ∣ n}

  -- Let $SU$ be the union of $S_{1000, 2}$, $S_{1000, 3}$, and $S_{1000, 5}$
  let SU := (S 1000 2) ∪ S 1000 3 ∪ S 1000 5

  -- Let $P$ be the set of primes less than $1000$ not including $2, 3, 5$.
  let P := {n ∈ range 1000 | n.Prime} \ {2, 3, 5}
  -- By the given fact, $P$ has $165$ elements.
  have hPcard : #P = 165 := by rw [card_sdiff (by native_decide), hPrimesCard]; rfl

  -- Let $PL$ be the set of prime looking numbers less than $1000$.
  set PL := {n ∈ range 1000 | n.PrimeLooking}

  -- It is easy to see that every number less than 1000 is either in $\{1\}$, $SU$, $P$ or $PL$.
  have : range 1000 = {1} ∪ SU ∪ P ∪ PL := by
    apply subset_antisymm
    · intro n
      simp
      intro hnlt
      by_cases hnPrime : n.Prime
      <;> simp_all [P, PL, SU, S, Nat.PrimeLooking]
      <;> omega
    · apply union_subset
      · apply union_subset
        · apply union_subset
          · simp
          · apply union_subset
            · apply union_subset
              · simp [S]
              · simp [S]
            · simp [S]
        · intro n
          simp [P]
          intros
          assumption
      · simp [PL]

  -- Moreover, the sets $\{1\}$, $SU$, $P$ and $PL$ are clearly pairwise disjoint.
  have hd₁ : Disjoint ({1} ∪ SU ∪ P) PL := by
    rw [Finset.disjoint_iff_ne]
    rintro a ha _ haPL rfl
    simp [mem_union, mem_singleton, SU, S] at ha
    rcases ha with (rfl | ⟨halt, h2dvda⟩ | ⟨halt, h3dvda⟩ | ⟨halt, h5dvda⟩ | hap)
    · simp [PL, Nat.PrimeLooking] at haPL
    · simp [PL, Nat.PrimeLooking] at haPL
      omega
    · simp [PL, Nat.PrimeLooking] at haPL
      omega
    · simp [PL, Nat.PrimeLooking] at haPL
      omega
    · simp [PL, Nat.PrimeLooking] at haPL
      simp [P] at hap
      exact haPL.2.2.1 hap.1.2

  have hd₂ : Disjoint ({1} ∪ SU) P := by
    rw [disjoint_iff_ne]
    intro a ha b hb hab
    simp [mem_union, mem_singleton, SU, S] at ha
    rcases ha with (rfl | ⟨ha, h2a⟩ | ⟨ha, h3a⟩ | ⟨ha, h5a⟩)
    · simp [←hab, P, Nat.Prime] at hb
    · simp [←hab, P] at hb
      have := hb.2.1
      contrapose! this
      symm
      rw [←Nat.prime_dvd_prime_iff_eq (by decide) hb.1.2]
      exact h2a
    · simp [←hab, P] at hb
      replace := hb.2.2.1
      contrapose! this
      symm
      rw [←Nat.prime_dvd_prime_iff_eq (by decide) hb.1.2]
      exact h3a
    · simp [←hab, P] at hb
      have := hb.2.2.2
      contrapose! this
      symm
      rw [←Nat.prime_dvd_prime_iff_eq (by decide) hb.1.2]
      exact h5a

  have hd₃ : Disjoint {1} SU := by
    intro
    simp
    rintro (rfl | rfl)
    <;> simp [SU, S]


  have hUnion: #({1} ∪ SU ∪ P ∪ PL) = 1000 := by rw [←this, card_range]

  -- Hence, the number of prime-looking numbers is
  -- $1000 - (168-3) - 1 - |S_{1000, 2} \cup S_{1000, 3} \cup S_{1000, 5}| = 834 - |SU|$
  -- (note that $2,3,5$ are primes).
  have : 1000 = 1 + #SU + 165 + #PL := by
    rw [←hUnion, card_union_of_disjoint hd₁, card_union_of_disjoint hd₂, card_union_of_disjoint hd₃,
        hPcard, card_singleton]
  have : #SU + #PL = 834 := by linarith
  have hPL : #PL = 834 - #SU := by exact Nat.eq_sub_of_add_eq' this
  rw [hPL]
  suffices #SU = 734 from (by linarith)
  suffices #SU = Nat.cast (R := ℤ) 734 from (by rw [←Nat.cast_inj (R := ℤ)]; exact this)

  -- This is the inclusion-exclusion principle.
  have (A B C : Finset ℕ) :
      #(A ∪ B ∪ C) = (#A : ℤ) + #B + #C - #(A ∩ B) - #(A ∩ C) - #(B ∩ C) + #(A ∩ B ∩ C) := by
    -- To prove it, we will use the property $|A \cup B| = |A| + |B| - |A \cap B|$
    -- repeatedly and simplify.
    rw [card_union]

    rw [Nat.cast_sub]; swap
    · apply Nat.le_add_right_of_le
      gcongr
      apply inter_subset_left

    rw [card_union, Nat.cast_add]

    rw [Nat.cast_sub]; swap
    · apply Nat.le_add_right_of_le
      gcongr
      apply inter_subset_left

    rw [Nat.cast_add, union_inter_distrib_right, card_union,
        inter_assoc, inter_comm B C, ←inter_assoc C C B, inter_self,
        inter_comm C B, ←inter_assoc]

    rw [Nat.cast_sub]; swap
    · apply Nat.le_add_right_of_le
      gcongr
      apply inter_subset_left

    rw [Nat.cast_add]

    linarith

  -- We can calculate $S_2 \cup S_3 \cup S_5$ using the
  -- [Principle of Inclusion-Exclusion](https://artofproblemsolving.com/wiki/index.php/Principle_of_Inclusion-Exclusion):
  rw [this]

  -- We need to find the number of elements of each set in this expression, including the
  -- pairwise and triple intersections

  -- When $p$ and $q$ are coprime, $p \cdot q | N$ iff $p | N$ and $q | N$.
  -- Therefore, $S_{N, p \cdot q} = S_{N, p} \cap S_{N, q}$.
  have hInterS {N p q : ℕ} (hpq : p.Coprime q) : S N p ∩ S N q = S N (p * q) := by
    ext n
    simp [S]
    constructor
    · rintro ⟨⟨hnlt, hpn⟩, ⟨_, hqn⟩⟩
      refine ⟨hnlt, ?_⟩
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hpq hpn hqn
    · rintro ⟨hnlt, hpqn⟩
      refine ⟨⟨hnlt, ?_⟩, ⟨hnlt, ?_⟩⟩
      <;> calc _ ∣ p * q := by simp
               _ ∣ n := by exact hpqn

  -- So, we can get rid off intersections because $2, 3$ and $5$ are pairwise coprime.
  rw [hInterS (by decide), hInterS (by decide), hInterS (by decide), hInterS (by decide)]

  -- Now, let's calculate $|S_{N + 1, p}|$ for $N + 1$. Divide $N$ by $p$ and write
  -- $N = p * \lfloor N / p \rfloor$. Then, elements of $S_{N + 1, p}$ are $p, 2p, \dots,
  -- \lfloor N / p \rfloor p$.
  have hS {N p : ℕ} (hp : 0 < p) : S (N + 1) p = image (fun x => p * x) (range (N / p + 1)) := by
    ext n
    simp [S]
    constructor
    · rintro ⟨hnlt, ⟨x, rfl⟩⟩
      use x
      refine ⟨?_, rfl⟩
      rw [Nat.lt_add_one_iff, mul_comm] at hnlt
      rw [Nat.lt_add_one_iff, Nat.le_div_iff_mul_le]
      · exact hnlt
      · exact hp
    · rintro ⟨x, hxlt, rfl⟩
      refine ⟨?_, by apply Nat.dvd_mul_right⟩
      rw [Nat.lt_add_one_iff, Nat.le_div_iff_mul_le] at hxlt
      rw [Nat.lt_add_one_iff, mul_comm]
      · exact hxlt
      · exact hp

  -- So, $|S_{N + 1, p}| = \lfloor N / p \rfloor + 1$.
  have hCardS {N p : ℕ} (hp : 0 < p) : #(S (N + 1) p) = N / p + 1 := by
    rw [hS hp, card_image_of_injective, card_range]
    intro x₁ x₂ hx₁x₂
    apply Nat.eq_of_mul_eq_mul_left (n := p) ?_ hx₁x₂
    apply Nat.zero_lt_of_ne_zero
    contrapose! hp
    rw [hp]

  -- Substituting these values into the expression, we get the answer.
  rw [hCardS (by decide), hCardS (by decide), hCardS (by decide), hCardS (by decide),
      hCardS (by decide), hCardS (by decide), hCardS (by decide)]
  simp