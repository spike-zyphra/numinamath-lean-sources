import Mathlib

/-
Simplify the congruences.\
Let $k = n+j$. Since $n$ and $j$ are integers, $k$ must also be an integer.\
The congruences can be rewritten in terms of $k$:\
(P1) $k \\equiv 0 \\pmod 2$\
(P2) $k \\equiv 0 \\pmod 3$\
(P3) $k \\equiv 1 \\pmod 4$\
(P4) $k \\equiv 5 \\pmod 6$\
(P5) $k \\equiv 7 \\pmod {12}$
-/
lemma lemma_1
  (k : ℤ)
  : k ≡ 0  [ZMOD 2]
  ∨ k ≡ 0  [ZMOD 3]
  ∨ k ≡ 1  [ZMOD 4]
  ∨ k ≡ 5  [ZMOD 6]
  ∨ k ≡ 7  [ZMOD 12] :=
by
  by_contra H
  push_neg at H
  rcases H with ⟨H1, H2, H3, H4, H5⟩
  have k_odd : Odd k := by
    by_contra h
    simp at h
    rcases h with ⟨k', h⟩
    subst h
    apply H1
    ring_nf
    simp [Int.ModEq]
  have A : k ≡ 3 [ZMOD 4] := by
    generalize kh : k % 4 = k4
    have : k4 < 4 := by
      rw [←kh]
      apply Int.emod_lt_of_pos
      simp
    have := @Int.emod_nonneg k 4 (by simp)
    rw [kh] at this
    simp [Int.ModEq]
    rcases k_odd with ⟨k', H⟩
    interval_cases k4
    . rw [H] at kh
      simp at kh
      omega
    . simp [Int.ModEq] at H3
      tauto
    . subst H
      omega
    . assumption
  have : ¬ k ≡ 2 [ZMOD 3] := by
    intro h
    apply H4
    simp [Int.ModEq] at A h ⊢
    omega
  have B : k ≡ 1 [ZMOD 3] := by
    simp [Int.ModEq] at this H2 ⊢
    generalize kh : k % 3 = u
    have : u < 3 := by
      simp [←kh]
      apply Int.emod_lt_of_pos
      simp
    have : u ≥ 0 := by
      simp [←kh]
      apply Int.emod_nonneg
      simp
    interval_cases u
    . omega
    . rfl
    . omega
  apply H5
  simp [Int.ModEq] at A B ⊢
  omega

/- Let $j$ be an integer. Show that for any integer $n$, at least one of the following congruences holds:
$n \equiv -j \pmod 2$, or
$n \equiv -j \pmod 3$, or
$n \equiv 1-j \pmod 4$, or
$n \equiv 5-j \pmod 6$, or
$n \equiv 7-j \pmod {12}$.  -/
theorem number_theorem_636438 (j : ℤ) (n : ℤ) :
    n ≡ -j [ZMOD 2]
  ∨ n ≡ -j [ZMOD 3]
  ∨ n ≡ 1 - j [ZMOD 4]
  ∨ n ≡ 5 - j [ZMOD 6]
  ∨ n ≡ 7 - j [ZMOD 12] :=
by
  -- use the lemma we have shown
  have := lemma_1 (n + j)
  rcases this with
    (h | h | h | h | h)
  all_goals
    simp [Int.ModEq] at h ⊢
    omega
