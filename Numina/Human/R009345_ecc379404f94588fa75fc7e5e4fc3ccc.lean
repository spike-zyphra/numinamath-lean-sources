import Mathlib

open Classical

/-Let $A$ be a set of positive integers containing the number 1 and at least one more element. Given that for any two different elements $m, n$ of $A$ the number $\frac{m+1}{(m+1, n+1)}$ is also an element of $A$, prove that $A$ coincides with the set of positive integers.-/
theorem number_theory_604458 (A : Set ℕ) (Apos : ∀ x ∈ A, 0 < x) (Acard : 2 ≤ A.ncard) (mem1 : 1 ∈ A)
(hmem : ∀ m ∈ A, ∀ n ∈ A, m ≠ n → (m + 1) / (m + 1).gcd (n + 1) ∈ A) : A = {n | 0 < n} := by
-- Prove that there exists some number $a$ belongs to $A$ such that $A$ is greater than $1$
  have EX : ∃ a ∈ A, 1 < a := by
    obtain ⟨S, ⟨Ssubs, Scard⟩⟩ := Set.exists_subset_card_eq Acard
    rw [Set.ncard_eq_two] at Scard; rcases Scard with ⟨x, y, ⟨xney, hS⟩⟩
    simp [Set.ext_iff] at hS; simp [Set.subset_def] at Ssubs; by_cases hx : x ≠ 1
    · use x; specialize hS x; simp at hS
      specialize Ssubs x hS; specialize Apos x Ssubs
      exact And.intro Ssubs (by omega)
    push_neg at hx; rw [hx] at xney; symm at xney; use y
    specialize hS y; simp at hS; specialize Ssubs y hS
    specialize Apos y Ssubs; exact And.intro Ssubs (by omega)
-- Write out all the properties we need about the smallest $a$ satisfying EX
  obtain ⟨amem, agt1⟩ := Nat.find_spec EX; have lta := Nat.le_find_iff EX (Nat.find EX)
  set a := Nat.find EX; replace lta : ∀ m < a, m ∈ A → m = 1 := by
    intro m hm mmem; specialize Apos m mmem
    simp at lta; specialize lta m hm mmem; omega
-- Use two-step induction to show for any $n$ greater or equal to $a$, $n$ belongs to $A$.
  have bigmem : ∀ n ≥ a, n ∈ A := by
    intro n; induction n using Nat.twoStepInduction with
    | zero => intro; omega
    | one => intro; omega
    | more n ihn ihn' =>
      intro hn; by_cases h : n < a - 1
      · replace h : n = a - 2 := by omega
        rw [h, Nat.sub_add_cancel (by omega)]; exact amem
      by_cases h' : n < a
      · replace h' : n = a - 1 := by omega
        rw [h', show 2 = 1+1 by simp, ← add_assoc, Nat.sub_add_cancel (by omega)]
        specialize hmem a amem 1 mem1 (by omega); norm_num at hmem
        suffices : (a + 1).gcd 2 = 1
        · simp [this] at hmem; exact hmem
        by_contra! h''; have : (a + 1).gcd 2 ∣ 2 := by exact Nat.gcd_dvd_right (a + 1) 2
        rw [Nat.Prime.dvd_iff_eq Nat.prime_two h''] at this
        rw [← this] at hmem; specialize lta ((a+1)/2) (by omega) hmem
        replace lta : a = 2 := by omega
        simp [lta] at h''
      specialize ihn (by omega); specialize ihn' (by omega)
      specialize hmem (n+1) ihn' n ihn (by simp)
      simp at hmem; rw [show n+1+1 = n+2 by ring] at hmem
      exact hmem
-- Prove $a=2$ by contradiction, we reduce it to the fact that $2$ belongs to $a$
  have aeq2 : a = 2 := by
    specialize hmem (2*a-1) (by apply bigmem; omega) (3*a-1) (by apply bigmem; omega) (by omega)
    repeat rw [Nat.sub_add_cancel] at hmem
    rw [Nat.gcd_mul_right] at hmem; norm_num at hmem
    rw [Nat.mul_div_left] at hmem
    by_contra! h; rw [ne_iff_lt_or_gt, gt_iff_lt] at h
    rcases h with _|h; omega
    specialize lta 2 h hmem; all_goals omega
-- The goal follows if we rewrite $a=2$ at bigmem
  rw [aeq2] at bigmem; simp [Set.ext_iff]
  intro x; by_cases hx : x ≤ 1
  · constructor; apply Apos
    intro; replace hx : x = 1 := by omega
    rw [hx]; exact mem1
  constructor; apply Apos
  intro; apply bigmem; omega