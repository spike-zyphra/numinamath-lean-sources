import Mathlib

open Finset

/-Soit $\mathrm{f}: \mathbb{N}^{\star} \rightarrow \mathbb{N}^{\star}$ une fonction telle que pour tout entier $\mathrm{n} \geqslant 1, \mathrm{f}(\mathrm{f}(\mathrm{n}))$ soit égal au nombre de diviseurs positifs de $n$. Montrer que si $p$ est un nombre premier, alors $f(p)$ est aussi un nombre premier.-/
theorem number_theory_607382 (f : ℕ → ℕ) (fpos : ∀ n, 0 < n → 0 < f n)
(hf : ∀ n, f (f n) = n.divisors.card) : ∀ p, Nat.Prime p → Nat.Prime (f p) := by
-- Prove a lemma saying that if $n$ has exactly $2$ divisors if and only if $n$ is prime
  have lm : ∀ n : ℕ, n.divisors.card = 2 ↔ n.Prime := by
    intro n; constructor
    · intro h; have : 2 ≤ n := by by_contra!; interval_cases n; any_goals simp at h
      rw [Nat.prime_def]; constructor; exact this; intro m mdvd
      replace h : n.divisors = {1, n} := by
        have auxcard : ({1, n} : Finset ℕ).card = 2 := by
          rw [card_eq_two]; use 1; use n; simp; linarith
        have : {1, n} ⊆ n.divisors := by simp [subset_iff]; linarith
        apply eq_iff_card_le_of_subset at this; simp [h, auxcard] at this
        symm; exact this
      replace mdvd : m ∈ n.divisors := by simp; constructor; exact mdvd; linarith
      rw [h] at mdvd; simp at mdvd; exact mdvd
    intro npr; simp [npr.divisors, card_eq_two]; use 1; use n; simp
    exact Ne.symm npr.ne_one
-- Prove a lemma saying that if $n$ has exactly $1$ divisors if and only if $n$ is $1$
  have lm' : ∀ n ≠ 0, n.divisors.card = 1 ↔ n = 1 := by
    intro n nne; constructor
    · intro hn; rw [card_eq_one] at hn; rcases hn with ⟨a, ha⟩
      simp [Finset.ext_iff] at ha; have := (ha 1).mp (by simp; exact nne)
      have := (ha n).mp (by simp; exact nne); linarith
    intro hn; simp [hn]
-- Specializing $hf$ at a prime number $p$, we get $f(f(p))=2$ for any prime $p$. Then rewrite the goal to proving $f(2)=2$
  intro p ppr; rw [← lm, ← hf]; have hfp : ∀ p, p.Prime → f (f p) = 2 := by
    intro q qpr; rw [hf, qpr.divisors, card_eq_two]; use 1; use q; simp
    exact Ne.symm qpr.ne_one
-- Prove that $f(2)$ is equal to the number of its divisors, which implies all the numbers $1, 2, ... f(2)$ divides $f(2)$
  rw [hfp p ppr]; have ff2 := hf (f 2); rw [hfp 2 Nat.prime_two] at ff2
  have auxsubs : (f 2).divisors ⊆ Icc 1 (f 2) := by
    simp [subset_iff]; intro d hd _; specialize fpos 2 (by simp); constructor
    · apply Nat.pos_of_dvd_of_pos at hd; specialize hd fpos; linarith
    apply Nat.le_of_dvd; all_goals assumption
  apply eq_iff_card_le_of_subset at auxsubs; simp [← ff2] at auxsubs; by_cases h : 2 < f 2
  -- If $f(2)$ is greater than $2$, then we can get a contradiction from $f(2)-1$ divides $f(2)$
  · have : f 2 - 1 ∣ f 2 := by
      suffices : f 2 - 1 ∈ Icc 1 (f 2); simp [← auxsubs] at this; exact this.left
      simp; rw [Nat.le_sub_iff_add_le]; all_goals linarith
    nth_rw 2 [show f 2 = f 2 - 1 + 1 by rw [Nat.sub_add_cancel]; linarith] at this
    simp [Nat.dvd_add_self_left] at this; linarith
  push_neg at h; have := fpos 2 (by simp); interval_cases hf2 : f 2
  -- If $f(2)=1$, we can get a contradiction from computing $f(4)$
  · have hfp' : ∀ p, p.Prime → f p = 1 := by
      intro p ppr; specialize fpos p ppr.pos; suffices : (f p).divisors.card = 1
      · rw [card_eq_one] at this; rcases this with ⟨a, ha⟩
        simp [Finset.ext_iff] at ha; have := (ha 1).mp (by simp; linarith)
        have := (ha (f p)).mp (by simp; linarith); linarith
      rw [← hf, hfp p ppr, hf2]
    have : Nat.divisors 4 = {1, 2, 4} := by decide
    apply_fun fun t => t.card at this; simp [← hf] at this
    apply_fun f at this; rw [hfp' 3 Nat.prime_three, hf (f 4), lm'] at this
    apply_fun f at this; rw [hf, show Nat.divisors 4 = {1, 2, 4} by decide] at this; simp at this
    rw [← hf2, hfp 2 Nat.prime_two] at this; linarith
    specialize fpos 4 (by simp); linarith
-- The only possibility is $f(2)=2$
  rfl